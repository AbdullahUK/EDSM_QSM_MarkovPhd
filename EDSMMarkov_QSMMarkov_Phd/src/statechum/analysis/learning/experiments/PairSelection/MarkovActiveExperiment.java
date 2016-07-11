/* Copyright (c) 2013 The University of Sheffield.
 * 
 * This file is part of StateChum.
 * 
 * StateChum is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * StateChum is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with StateChum.  If not, see <http://www.gnu.org/licenses/>.
 */

package statechum.analysis.learning.experiments.PairSelection;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Stack;
import java.util.concurrent.Callable;
import java.util.concurrent.atomic.AtomicLong;

import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;
import statechum.Configuration;
import statechum.Configuration.QuestionGeneratorKind;
import statechum.Configuration.STATETREE;
import statechum.Configuration.ScoreMode;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.DeterministicDirectedSparseGraph.VertID;
import statechum.GlobalConfiguration;
import statechum.GlobalConfiguration.G_PROPERTIES;
import statechum.Label;
import statechum.Pair;

import statechum.analysis.learning.DrawGraphs;
import statechum.analysis.learning.DrawGraphs.RBoxPlotCvs;
import statechum.analysis.learning.DrawGraphs.RGraph;
import statechum.analysis.learning.DrawGraphs.RWilcoxon;
import statechum.analysis.learning.MarkovClassifier;
import statechum.analysis.learning.MarkovClassifier.ConsistencyChecker;
import statechum.analysis.learning.AbstractOracle;
import statechum.analysis.learning.MarkovModel;
import statechum.analysis.learning.PairScore;
import statechum.analysis.learning.experiments.ExperimentRunner;
import statechum.analysis.learning.experiments.PaperUAS;
import statechum.analysis.learning.experiments.SGE_ExperimentRunner.RunSubExperiment;
import statechum.analysis.learning.experiments.SGE_ExperimentRunner.processSubExperimentResult;
import statechum.analysis.learning.experiments.PairSelection.Cav2014.EDSMReferenceLearner;
import statechum.analysis.learning.experiments.mutation.DiffExperiments.MachineGenerator;
import statechum.analysis.learning.observers.ProgressDecorator.LearnerEvaluationConfiguration;
import statechum.analysis.learning.rpnicore.AMEquivalenceClass;
import statechum.analysis.learning.rpnicore.AbstractLearnerGraph;
import statechum.analysis.learning.rpnicore.ComputeQuestions;
import statechum.analysis.learning.rpnicore.LearnerGraph;
import statechum.analysis.learning.rpnicore.LearnerGraphCachedData;
import statechum.analysis.learning.rpnicore.LearnerGraphND;
import statechum.analysis.learning.rpnicore.MergeStates;
import statechum.analysis.learning.rpnicore.RandomPathGenerator;
import statechum.analysis.learning.rpnicore.RandomPathGenerator.RandomLengthGenerator;
import statechum.analysis.learning.rpnicore.Transform;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;
import statechum.analysis.learning.rpnicore.WMethod;
import statechum.model.testset.PTASequenceEngine.FilterPredicate;
import statechum.collections.ArrayMapWithSearchPos;


public class MarkovActiveExperiment extends PairQualityLearner
{
	public static class LearnerRunner implements Callable<ThreadResult>
	{
		protected final Configuration config;
		protected final ConvertALabel converter;
		protected final int states,sample,trainingSample;
		protected boolean onlyUsePositives;
		protected final int seed;
		protected int chunkLen=3;
		protected int traceQuantity;
		protected String selectionID;
		protected double alphabetMultiplier = 1;
		protected double traceLengthMultiplier = 1;

		protected double tracesAlphabetMultiplier = 0;
		
		/** Whether we should try learning with zero inconsistencies, to see how heuristics fare. */
		protected boolean disableInconsistenciesInMergers = false;
		
		public void setDisableInconsistenciesInMergers(boolean v)
		{
			disableInconsistenciesInMergers = v;
		}
		
		public void setTracesAlphabetMultiplier(double evalAlphabetMult)
		{
			tracesAlphabetMultiplier = evalAlphabetMult;
		}
		
		public void setSelectionID(String value)
		{
			selectionID = value;
		}
		
		/** Whether to filter the collection of traces such that only positive traces are used. */
		public void setOnlyUsePositives(boolean value)
		{
			onlyUsePositives = value;
		}
		
		public void setAlphabetMultiplier(double mult)
		{
			alphabetMultiplier = mult;
		}
		
		public void setTraceLengthMultiplier(double traceMulti) {
			traceLengthMultiplier=traceMulti;
		}
		
		public void setTraceQuantity(int traceQuantity2) {
			traceQuantity=	traceQuantity2;		
		}
		
		public void setChunkLen(int len)
		{
			chunkLen = len;
		}
		
		public LearnerRunner(int argStates, int argSample, int argTrainingSample, int argSeed, int nrOfTraces, Configuration conf, ConvertALabel conv)
		{
			states = argStates;sample = argSample;trainingSample = argTrainingSample;config = conf;seed = argSeed;traceQuantity=nrOfTraces;converter=conv;
		}
		
		boolean useCentreVertex = true, useDifferentScoringNearRoot = false, mergeIdentifiedPathsAfterInference = true, useClassifyToOrderPairs = true,useMostConnectedVertexToStartLearning = false;

		public void setlearningParameters(boolean useCentreVertexArg, boolean useDifferentScoringNearRootArg, boolean mergeIdentifiedPathsAfterInferenceArg, boolean useClassifyToOrderPairsArg, boolean useMostConnectedVertexToStartLearningArg)
		{
			useCentreVertex = useCentreVertexArg;useDifferentScoringNearRoot = useDifferentScoringNearRootArg;mergeIdentifiedPathsAfterInference = mergeIdentifiedPathsAfterInferenceArg;useClassifyToOrderPairs = useClassifyToOrderPairsArg;useMostConnectedVertexToStartLearning = useMostConnectedVertexToStartLearningArg; 
		}
		
		public void setPresetLearningParameters(int value)
		{
			switch(value)
			{
			case 0:// learning by not doing pre-merging, starting from root 
				setlearningParameters(false, false, false, false, false);break;
			case 1:// learning by doing pre-merging, starting from most connected vertex. This evaluates numerous pairs and hence is very slow.
				setlearningParameters(true, false, false, true, true);break;
			case 2:// learning by doing pre-merging but starting from root. This seems similar to preset 1 on 20 states.
				setlearningParameters(true, false, false, false, false);break;
			case 3:// learning by not doing pre-merging, starting from root and using a heuristic around root 
				setlearningParameters(false, true, false, true, false);break;
			case 4:// learning by not doing pre-merging, starting from root and not ranking the top IScore candidates with the fanout metric.
				setlearningParameters(false, false, false, false, false);break;
			default:
				throw new IllegalArgumentException("invalid preset number");
			}
		}
		@Override
		public ThreadResult call() throws Exception 
		{
//			if (tracesAlphabetMultiplier <= 0)
//				tracesAlphabetMultiplier = alphabetMultiplier;
			final int alphabet = (int)(alphabetMultiplier*states);
//			
			LearnerGraph referenceGraph = null;
			ThreadResult outcome = new ThreadResult();
			MachineGenerator mg = new MachineGenerator(states, 400 , (int)Math.round((double)states/5));
			mg.setGenerateConnected(true);
			referenceGraph = mg.nextMachine(alphabet,sample, config, converter).pathroutines.buildDeterministicGraph();// reference graph has no reject-states, because we assume that undefined transitions lead to reject states.
//			Visualiser.updateFrame(referenceGraph, null);
			//			LearnerGraph referenceGraphAsText = FsmParser.buildLearnerGraph("q1-connect->q2-login->q3-setfiletype->q4-rename->q6-storefile->q5-setfiletype->q4-storefile->q7-appendfile->q5\nq3-makedir->q8-makedir->q8-logout->q16-disconnect->q1\nq3-changedirectory->q9-listnames->q10-delete->q10-changedirectory->q9\nq10-appendfile->q11-logout->q16\nq3-storefile->q11\nq3-listfiles->q13-retrievefile->q13-logout->q16\nq13-changedirectory->q14-listfiles->q13\nq7-logout->q16\nq6-logout->q16", "specgraph",config,converter);
//			referenceGraph = new LearnerGraph(config);AbstractPathRoutines.convertToNumerical(referenceGraphAsText,referenceGraph);
//		    referenceGraph = FsmParser.buildLearnerGraph("q0-open->q1-opendoors->q3-close->q5-closedoors->q0-start->q2-startmotor->q4-stop->q7-stopmotor->q0\nq6-highspeed->q9-lowspeed->q6-stop->q10-stopmotor->q13-start->q15-startmotor->q6\nq4-leavingstation->q6\nq9-approachingstation->q12-lowspeed->q8\nq6-approachingstation->q8-atstation->q4\nq8-stop->q11-stopmotor->q14-start->q16-startmotor->q8", "specgraph",config,converter);
//			referenceGraph = FsmParser.buildLearnerGraph("q1-anything_reset->q1-passive_open->q2\nq1-active_open_syn->q4\nq2-close->q1\nq2-syn_syn_ack->q3\nq2-send_syn->q4\nq3-reset->q2\nq3-ack->q5\nq3-close_fin->q7\nq4-close_timeout_reset->q1\nq4-syn_ack_ack->q5\nq4-syn_syn_ack->q3\nq5-fin_ack->q6\nq5-close_fin->q7\nq6-close_fin->q9\nq7-fin_ack->q8\nq7-ack->q10\nq7-fin_ack_ack->q11\nq8-ack->q11\nq9-ack->q1\nq10-fin_ack->q11-timeout->q1", "specgraph",config,converter);
//			referenceGraph = FsmParser.buildLearnerGraph("q1-CONNECT!->q2-VERSION?->q3\nq2-VERSION!->q4\nq3-VERSION!->q5\nq4-VERSION?->q5-KEXINIT!->q6\nq5-KEXINIT?->q7\nq6-KEXINIT?->q8\nq7-KEXINIT!->q8-KEXDH_INIT!->q9-KEXDH_REPLY?->q10\nq6-KEXDH_INIT!->q11-KEXINIT?->q12-KEXDH_REPLY?->q10-NEWKEYS?->q13\nq10-NEWKEYS!->q14\nq13-NEWKEYS!->q15\nq14-NEWKEYS?->q15-KEXINIT!->q6\nq15-KEXINIT?->q7", "specgraph",config,converter);
//			referenceGraph = FsmParser.buildLearnerGraph("q0-Load->q1-Close->q0-Exit->q3\nq1-Edit->q2-Save->q1-Exit->q3\nq2-Edit->q2-Exit->q3\nq2-Close->q0", "specgraph",config,converter);
//			referenceGraph = FsmParser.buildLearnerGraph("q1-connect->q2-login->q3-setfiletype->q4-rename->q6-storefile->q5-setfiletype->q4-storefile->q7-appendfile->q5\nq3-makedir->q8-makedir->q8-logout->q16-disconnect->q1\nq3-changedirectory->q9-listnames->q10-delete->q10-changedirectory->q9\nq10-appendfile->q11-logout->q16\nq3-storefile->q11\nq3-listfiles->q13-retrievefile->q13-logout->q16\nq13-changedirectory->q14-listfiles->q13\nq7-logout->q16\nq6-logout->q16", "specgraph",config,converter);
//			referenceGraph = FsmParser.buildLearnerGraph("q1-initialise->q2-connect->q3-login->q4-storefile->q14\nq4-changedir->q5\nq4-listfiles->q6\nq4-makedir->q7\nq4-setfiletype->q8\nq5-listnames->q9\nq6-retrievefile->q6-changedir->q10\nq6-logout->q15\nq7-makedir->q7-logout->q15\nq8-rename->q12\nq8-storefile->q11\nq9-delete->q9-appendfile->q14\nq10-listfiles->q6\nq11-appendfile->q13\nq12-storefile->q13\nq12-logout->q15\nq13-logout->q15\nq13-setfiletype->q8\nq14-logout->q15-disconnect->q1", "specgraph",config,converter);
//			LearnerGraph referenceGraphAsText = FsmParser.buildLearnerGraph("q1-initialise->q2-connect->q3-login->q4-storefile->q14\nq4-changedir->q5\nq4-listfiles->q6\nq4-makedir->q7\nq4-setfiletype->q8\nq5-listnames->q9\nq6-retrievefile->q6-changedir->q10\nq6-logout->q15\nq7-makedir->q7-logout->q15\nq8-rename->q12\nq8-storefile->q11\nq9-delete->q9-appendfile->q14\nq10-listfiles->q6\nq11-appendfile->q13\nq12-storefile->q13\nq12-logout->q15\nq13-logout->q15\nq13-setfiletype->q8\nq14-logout->q15-disconnect->q1\nq9-changedir->q5", "specgraph",config,converter);

//			LearnerGraph referenceGraph = new LearnerGraph(config);AbstractPathRoutines.convertToNumerical(referenceGraphAsText,referenceGraph);
//			final int states = referenceGraph.getStateNumber(), alphabet = referenceGraph.pathroutines.computeAlphabet().size();

			LearnerEvaluationConfiguration learnerEval = new LearnerEvaluationConfiguration(config);
			learnerEval.setLabelConverter(converter);
			Collection<List<Label>> testSet = new ArrayList<List<Label>>();
//			testSet.addAll(referenceGraph.wmethod.getFullTestSet(4));
			testSet.addAll(PaperUAS.computeEvaluationSet(referenceGraph, states*3, makeEven(states*states*2)));
   		
		   
			SampleData dataSample = new SampleData(null,null);



			  
			// try learning the same machine using a random generator selector passed as a parameter.
			LearnerGraph pta = new LearnerGraph(config);
			RandomPathGenerator generator = new RandomPathGenerator(referenceGraph,new Random(trainingSample),(5),null);
			final int tracesToGenerate = makeEven(traceQuantity);
			generator.generateRandomPosNeg(tracesToGenerate, 1, false, new RandomLengthGenerator() {
									
					@Override
					public int getLength() {
						return (int)(traceLengthMultiplier*states*states*2);
					}
	
					@Override
					public int getPrefixLength(int len) {
						return len;
					}
				});


			if (onlyUsePositives)
			{
				pta.paths.augmentPTA(generator.getAllSequences(0).filter(new FilterPredicate() {
					@Override
					public boolean shouldBeReturned(Object name) {
						return ((statechum.analysis.learning.rpnicore.RandomPathGenerator.StateName)name).accept;
					}
				}));
			}
			else
				pta.paths.augmentPTA(generator.getAllSequences(0));
	
			final MarkovModel m= new MarkovModel(chunkLen,true,true,false);
			new MarkovClassifier(m, pta).updateMarkov(false);// construct Markov chain if asked for.
			pta.clearColours();

			if (!onlyUsePositives)
				assert pta.getStateNumber() > pta.getAcceptStateNumber() : "graph with only accept states but onlyUsePositives is not set";
			else 
				assert pta.getStateNumber() == pta.getAcceptStateNumber() : "graph with negatives but onlyUsePositives is set";
			
				
			
			final Configuration deepCopy = pta.config.copy();
			deepCopy.setLearnerCloneGraph(true);
			

			LearnerGraph trimmedReference = MarkovPassivePairSelection.trimUncoveredTransitions(pta,referenceGraph);
			final ConsistencyChecker checker = new MarkovClassifier.DifferentPredictionsInconsistencyNoBlacklistingIncludeMissingPrefixes();
			long inconsistencyForTheReferenceGraph = MarkovClassifier.computeInconsistency(referenceGraph, m, checker,false);

			LearnerGraph ptaToUseForInference = pta;
			final LearnerGraph freferenceGraph=referenceGraph;		
			System.out.println();
	
			dataSample.referenceinconsistency=(double) inconsistencyForTheReferenceGraph;

			
			// This ModifiedQSM Learner
			{
				dataSample.modifiedQSM = zeroScore;
				learnerEval.config.setAskQuestions(false);
				learnerEval.config.setRecomputeScore(true);
				learnerEval.config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
				learnerEval.config.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph actualAutomaton = null;
			    ptaToUseForInference = new LearnerGraph(deepCopy);
				LearnerGraph.copyGraphs(pta, ptaToUseForInference);
				assert ptaToUseForInference.getStateNumber() == pta.getStateNumber();
			
				ModifiedQSM ModifiedQSMWithoutMarkov = new ModifiedQSM(learnerEval,ptaToUseForInference,0)
				{				
					@Override
					public Pair<Integer,String> CheckWithEndUser(
						@SuppressWarnings("unused")	LearnerGraph model,
						List<Label> question, @SuppressWarnings("unused") int valueForNoRestart,
						@SuppressWarnings("unused") List<Boolean> acceptedElements,
						@SuppressWarnings("unused") PairScore pairBeingMerged,
						@SuppressWarnings("unused")   final Object [] moreOptions) 
					 {							
						Pair<Integer,String> answer = new Pair<Integer,String>(freferenceGraph.paths.tracePathPrefixClosed(question),null);
						NumberOfMarkovQuestions++;
//							System.out.println(question + "  "+NumberOfMarkovQuestions);
						return answer;
					 }					
				};							
				LearnerGraph ptaCopy = new LearnerGraph(deepCopy);
				LearnerGraph.copyGraphs(pta, ptaCopy);
				ModifiedQSMWithoutMarkov.setquestionPTA(ptaCopy);
				assert ModifiedQSMWithoutMarkov.NumberOfMarkovQuestions == 0;
				LearnerGraph ptaquestion = new LearnerGraph(deepCopy);
				//LearnerGraph.copyGraphs(pta, ptaquestion);
				ModifiedQSMWithoutMarkov.setquestionOnlyPTA(ptaquestion);
				assert ptaquestion.getStateNumber()==1;
				// either to drop queries using inconsistecy or not
				ModifiedQSMWithoutMarkov.setinconsistencycheck(false);
				MarkovModel MarkovModel= new MarkovModel(chunkLen,true,true,false);
				new MarkovClassifier(MarkovModel, ptaCopy).updateMarkov(false);

				ModifiedQSMWithoutMarkov.setMarkov(MarkovModel);
				ModifiedQSMWithoutMarkov.setChecker(checker);
				ModifiedQSMWithoutMarkov.setReference(referenceGraph);
				ModifiedQSMWithoutMarkov.setOption(1);
				ModifiedQSMWithoutMarkov.setEalierBlocking(true);
				actualAutomaton = ModifiedQSMWithoutMarkov.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
				LearnerGraph Markovpta = new LearnerGraph(config);
				Markovpta.initPTA();						
				Markovpta=ModifiedQSMWithoutMarkov.getquestioncoregraph();
				
				int NumberOfMarkovQueries=0;
				for(CmpVertex c:Markovpta.transitionMatrix.keySet())
				{
					if(Markovpta.transitionMatrix.get(c).values().size()==0)
						NumberOfMarkovQueries++;
				}
				
				System.out.println("The Number of modifiedQSM Queries is ="+ModifiedQSMWithoutMarkov.NumberOfMarkovQuestions+" Number of states: "+actualAutomaton.getStateNumber()+ " where reference: "+referenceGraph.getStateNumber());	

//				System.out.println("The Number of modifiedQSM Queries using earlier blocking Based on Dupont is ="+NumberOfMarkovQueries+" originalQueries="+SymmetricearlierblockinglearnerOfPairs.NumberOfMarkovQuestions+" Number of states: "+actualAutomaton.getStateNumber()+ " where reference: "+referenceGraph.getStateNumber());	

				VertID rejectVertexID = null;
				for(CmpVertex v:actualAutomaton.transitionMatrix.keySet())
					if (!v.isAccept())
					{
						assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
						rejectVertexID = v;break;
					}
				if (rejectVertexID == null)
					rejectVertexID = actualAutomaton.nextID(false);
				actualAutomaton.pathroutines.completeGraphPossiblyUsingExistingVertex(rejectVertexID);// we need to complete the graph, otherwise we are not matching it with the original one that has been completed.
				dataSample.modifiedQSM = estimateDifference(referenceGraph,actualAutomaton,testSet);
				dataSample.modifiedQSM.numberofMQ=ModifiedQSMWithoutMarkov.NumberOfMarkovQuestions;
				dataSample.modifiedQSM.numberofQuestions=NumberOfMarkovQueries;
				dataSample.modifiedQSM.selectionid = selectionID;
				dataSample.modifiedQSM.numerofstates=states;
			}
				
			// This MarkovQSM option 2
			{
				dataSample.markovQSM = zeroScore;
				learnerEval.config.setAskQuestions(false);
				learnerEval.config.setRecomputeScore(true);
				learnerEval.config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
				learnerEval.config.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph actualAutomaton = null;
			    ptaToUseForInference = new LearnerGraph(deepCopy);
				LearnerGraph.copyGraphs(pta, ptaToUseForInference);
				assert ptaToUseForInference.getStateNumber() == pta.getStateNumber();
				
				ModifiedQSM ModifiedQSMWithMarkov = new ModifiedQSM(learnerEval,ptaToUseForInference,0)
				{				
					@Override
					public Pair<Integer,String> CheckWithEndUser(
						@SuppressWarnings("unused")	LearnerGraph model,
						List<Label> question, @SuppressWarnings("unused") int valueForNoRestart,
						@SuppressWarnings("unused") List<Boolean> acceptedElements,
						@SuppressWarnings("unused") PairScore pairBeingMerged,
						@SuppressWarnings("unused")   final Object [] moreOptions) 
					 {							
						Pair<Integer,String> answer = new Pair<Integer,String>(freferenceGraph.paths.tracePathPrefixClosed(question),null);
						NumberOfMarkovQuestions++;
						return answer;
					 }					
				};							
				LearnerGraph ptaCopy = new LearnerGraph(deepCopy);
				LearnerGraph.copyGraphs(pta, ptaCopy);
				ModifiedQSMWithMarkov.setquestionPTA(ptaCopy);
				assert ModifiedQSMWithMarkov.NumberOfMarkovQuestions == 0;
				LearnerGraph ptaquestion = new LearnerGraph(deepCopy);
				//LearnerGraph.copyGraphs(pta, ptaquestion);
				ModifiedQSMWithMarkov.setquestionOnlyPTA(ptaquestion);
				assert ptaquestion.getStateNumber()==1;
				// either to drop queries using inconsistecy or not
				ModifiedQSMWithMarkov.setinconsistencycheck(true);
				MarkovModel MarkovModel= new MarkovModel(chunkLen,true,true,false);
				new MarkovClassifier(MarkovModel, ptaCopy).updateMarkov(false);

				ModifiedQSMWithMarkov.setMarkov(MarkovModel);
				ModifiedQSMWithMarkov.setChecker(checker);
				ModifiedQSMWithMarkov.setReference(referenceGraph);
				ModifiedQSMWithMarkov.setOption(1);
				ModifiedQSMWithMarkov.setEalierBlocking(true);
				actualAutomaton = ModifiedQSMWithMarkov.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
				LearnerGraph Markovpta = new LearnerGraph(config);
				Markovpta.initPTA();						
				Markovpta=ModifiedQSMWithMarkov.getquestioncoregraph();
				
				int NumberOfMarkovQueries=0;
				for(CmpVertex c:Markovpta.transitionMatrix.keySet())
				{
					if(Markovpta.transitionMatrix.get(c).values().size()==0)
						NumberOfMarkovQueries++;
				}
				
				System.out.println("The Number of modifiedQSM Queries with Markov ="+ModifiedQSMWithMarkov.NumberOfMarkovQuestions+" Number of states: "+actualAutomaton.getStateNumber()+ " where reference: "+referenceGraph.getStateNumber());	

//							System.out.println("The Number of modifiedQSM Queries using earlier blocking Based on Dupont is ="+NumberOfMarkovQueries+" originalQueries="+SymmetricearlierblockinglearnerOfPairs.NumberOfMarkovQuestions+" Number of states: "+actualAutomaton.getStateNumber()+ " where reference: "+referenceGraph.getStateNumber());	

				VertID rejectVertexID = null;
				for(CmpVertex v:actualAutomaton.transitionMatrix.keySet())
					if (!v.isAccept())
					{
						assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
						rejectVertexID = v;break;
					}
				if (rejectVertexID == null)
					rejectVertexID = actualAutomaton.nextID(false);
				actualAutomaton.pathroutines.completeGraphPossiblyUsingExistingVertex(rejectVertexID);// we need to complete the graph, otherwise we are not matching it with the original one that has been completed.
				dataSample.markovQSM = estimateDifference(referenceGraph,actualAutomaton,testSet);
				dataSample.markovQSM.numberofMQ=ModifiedQSMWithMarkov.NumberOfMarkovQuestions;
				dataSample.markovQSM.numberofQuestions=NumberOfMarkovQueries;
				dataSample.markovQSM.selectionid = selectionID;
				dataSample.markovQSM.numerofstates=states;
			}
			
			
//           This is QSM reference
			{
				dataSample.referenceLearner=zeroScore;
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				evaluationConfig.setAskQuestions(true);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);			
				ptaToUseForInference = new LearnerGraph(deepCopy);
				LearnerGraph.copyGraphs(pta, ptaToUseForInference);
				assert ptaToUseForInference.getStateNumber() == pta.getStateNumber();
				try
				{
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					EDSMReferenceLearner ref = new Cav2014.EDSMReferenceLearner(referenceLearnerEval, ptaToUseForInference, 0)
					{
						
						@Override
						public Pair<Integer,String> CheckWithEndUser(
							@SuppressWarnings("unused")	LearnerGraph model,
							List<Label> question, @SuppressWarnings("unused") int valueForNoRestart,
							@SuppressWarnings("unused") List<Boolean> acceptedElements,
							@SuppressWarnings("unused") PairScore pairBeingMerged,
							@SuppressWarnings("unused")   final Object [] moreOptions) 
						 {						

							Pair<Integer,String> answer = new Pair<Integer,String>(referenceGraph.paths.tracePathPrefixClosed(question),null);
							numberofQuestion++;
							if(answer.firstElem==-3)
							{
								this.getQuestionPTA().paths.augmentPTA(question, true, false, null);
							}
							else
							{
								 LinkedList<Label> subAnswer = new LinkedList<Label>();
								 subAnswer.addAll(question.subList(0, answer.firstElem + 1));
								 this.getQuestionPTA().paths.augmentPTA(subAnswer, false, false, null);
							}
//							System.out.println(question + "  "+pairBeingMerged+" "+numberofQuestion);
//							System.out.println("Number Of QSM Questions= "+numberofQuestion);
							return answer;
						 }
					};
					LearnerGraph ptaCopy = new LearnerGraph(deepCopy);
					LearnerGraph.copyGraphs(pta, ptaCopy);
					ref.setquestioPTA(ptaCopy);
					ref.setReference(referenceGraph);
					outcomeOfReferenceLearner=ref.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					LearnerGraph QSMpta = new LearnerGraph(config);
					QSMpta.initPTA();	
					QSMpta=ref.getQuestionPTA();

					int QSMqueries=0;
					for(CmpVertex c:QSMpta.transitionMatrix.keySet())
					{
						if(QSMpta.transitionMatrix.get(c).values().size()==0)
							QSMqueries++;
					}
					System.out.println("The Number of QSM Queries is ="+ref.numberofQuestion +" Number of states: "+outcomeOfReferenceLearner.getStateNumber()+ " where reference: "+referenceGraph.getStateNumber());
					
					VertID rejectVertexID = null;
					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					outcomeOfReferenceLearner.pathroutines.completeGraphPossiblyUsingExistingVertex(rejectVertexID);// we need to complete the graph, otherwise we are not matching it with the original one that has been completed.
					dataSample.referenceLearner = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
					dataSample.referenceLearner.numberofMQ=ref.numberofQuestion;
					dataSample.referenceLearner.numberofQuestions=QSMqueries;
					dataSample.referenceLearner.selectionid = selectionID;
					dataSample.referenceLearner.numerofstates=states;

				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
				}
			}
			

		
			dataSample.fractionOfStatesIdentifiedBySingletons=Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph));
			dataSample.stateNumber = referenceGraph.getStateNumber();
			dataSample.transitionsSampled = Math.round(100*trimmedReference.pathroutines.countEdges()/referenceGraph.pathroutines.countEdges());
			statechum.Pair<Double,Double> correctnessOfMarkov = new MarkovClassifier(m, referenceGraph).evaluateCorrectnessOfMarkov();
			dataSample.markovPrecision = Math.round(100*correctnessOfMarkov.firstElem);
			dataSample.markovRecall = Math.round(100*correctnessOfMarkov.secondElem);
//			dataSample.comparisonsPerformed = learnerOfPairs.comparisonsPerformed;
			dataSample.traceNumber=traceQuantity;
			Collection<List<Label>> wset=WMethod.computeWSet_reducedw(referenceGraph);
			int wSeqLen=0;
			for(List<Label> seq:wset)
			{
				int len = seq.size();if (len > wSeqLen) wSeqLen=len;
			}
		/*	System.out.println("actual: "+actualAutomaton.getStateNumber()+" from reference learner: "+outcomeOfReferenceLearner.getStateNumber()+ 
					" difference actual is "+dataSample.actualLearner.differenceBCR+ " difference ref is "+dataSample.referenceLearner.differenceBCR
					+ " inconsistency learnt "+dataSample.actualLearner.inconsistency+" inconsistency reference: "+inconsistencyForTheReferenceGraph
					+" transitions per state: "+(double)referenceGraph.pathroutines.countEdges()/referenceGraph.getStateNumber()+
						" W seq max len "+wSeqLen+
						" Uniquely identifiable by W "+Math.round(100*MarkovClassifier.calculateFractionOfIdentifiedStates(referenceGraph, wset))+" %"
					+ " and by singletons "+Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph))+" %"
					);*/
			outcome.samples.add(dataSample);			
			return outcome;
		}

		// Delegates to a specific estimator
		ScoresForGraph estimateDifference(LearnerGraph reference, LearnerGraph actual,Collection<List<Label>> testSet)
		{
			ScoresForGraph outcome = new ScoresForGraph();
			outcome.differenceStructural=DifferenceToReferenceDiff.estimationOfDifferenceDiffMeasure(reference, actual, config, 1);
			outcome.differenceBCR=DifferenceToReferenceLanguageBCR.estimationOfDifference(reference, actual,testSet);
			System.out.println("bcr="+outcome.differenceBCR.getValue());
			System.out.println("diff="+outcome.differenceStructural.getValue());

			return outcome;
		}		
	}
	
			
	public static final ScoresForGraph zeroScore;
	static
	{
		zeroScore = new ScoresForGraph();zeroScore.differenceBCR=new DifferenceToReferenceLanguageBCR(0, 0, 0, 0);zeroScore.differenceStructural=new DifferenceToReferenceDiff(0, 0);
	}


	/** Uses the supplied classifier to rank pairs. */
	public static class ModifiedQSM extends LearnerThatCanClassifyPairs implements statechum.analysis.learning.rpnicore.PairScoreComputation.RedNodeSelectionProcedure
	{
		@SuppressWarnings("unused")
		@Override
		public CmpVertex selectRedNode(LearnerGraph gr,Collection<CmpVertex> reds, Collection<CmpVertex> tentativeRedNodes) 
		{
			return tentativeRedNodes.iterator().next();
		}
		
		public void setquestionPTA(LearnerGraph ptaCopy1) {
			questioncoregraph=ptaCopy1;			
		}
		
		public void setquestionOnlyPTA(LearnerGraph ptaCopy1) {
			questioncoregraphonly=ptaCopy1;			
		}
		
		public LearnerGraph getQuestionPTA(LearnerGraph ptaCopy1) {
			return questioncoregraph;		
		}

		
		public void setReference(LearnerGraph referenceGraph) {
			refgraph=referenceGraph;			
		}

		@SuppressWarnings("unused")
		@Override
		public CmpVertex resolvePotentialDeadEnd(LearnerGraph gr, Collection<CmpVertex> reds, List<PairScore> pairs) 
		{
			return null;												
		}
		public void setCenterVertex(CmpVertex vertexWithMostTransitions) {
			cenrtrevertexWithMostTransitions=vertexWithMostTransitions;			
		}
		
		public void setOption(int opt) {
			option=opt;
		}
		
		public void setEalierBlocking(boolean earlier) {
			earlierblockingmerger=earlier;
		}
		
		public LearnerGraph getquestioncoregraph() {
			return this.questioncoregraph;
		}
		
	    int option=0;
	    boolean earlierblockingmerger =false;
	    boolean CheckInconsistecy =false;
		
		long inconsistencyFromAnEarlierIteration = 0;
		LearnerGraph coregraph = null;
		LearnerGraph referencecoregraph = null;
		LearnerGraph questioncoregraph = null;
		LearnerGraph questioncoregraphonly = null;
		LearnerGraph Fullcoregraph = null;

		LearnerGraph extendedGraph = null;
		MarkovClassifier cl=null;
		LearnerGraphND inverseGraph = null;
		long comparisonsPerformed = 0;
		int NumberOfMarkovQuestions=0;
		LearnerGraph refgraph = null;
		CmpVertex cenrtrevertexWithMostTransitions = null;
		boolean useNewScoreNearRoot = false, useClassifyPairs = false;
		HashSet<PairScore> PairLists = new HashSet<PairScore>();
		ArrayList<List<Label>> negatives= new ArrayList<List<Label>> ();
		public void setinconsistencycheck(boolean incon)
		{
			CheckInconsistecy = incon;
		}
		
		public void setUseNewScoreNearRoot(boolean v)
		{
			useNewScoreNearRoot = v;
		}
		
		public void setUseClassifyPairs(boolean v)
		{
			useClassifyPairs = v;
		}
		
		Map<CmpVertex,Long> inconsistenciesPerVertex = null;
		
		/** Whether we should try learning with zero inconsistencies, to see how heuristics fare. */
		protected boolean disableInconsistenciesInMergers = false;
		
		public void setDisableInconsistenciesInMergers(boolean v)
		{
			disableInconsistenciesInMergers = v;
		}

		@Override
		public void initComputation(LearnerGraph graph) 
		{
			coregraph = graph;
			inverseGraph = (LearnerGraphND)MarkovClassifier.computeInverseGraph(coregraph,true);
			inconsistenciesPerVertex = new ArrayMapWithSearchPos<CmpVertex,Long>(coregraph.getStateNumber());
			cl=new MarkovClassifier(Markov,coregraph);
			if(CheckInconsistecy)
			{
//				System.out.println();
//				System.out.println(Markov.computePredictionMatrix());
				new MarkovClassifier(Markov,questioncoregraphonly).updateMarkov(true);
				cl=new MarkovClassifier(Markov,coregraph);
//				System.out.println(Markov.computePredictionMatrix());

			}
		}
		
		@Override // we only need this in order to supply a routine to find surrounding transitions and initComputation
		public long overrideScoreComputation(PairScore p) 
		{
			return computeScoreBasedOnInconsistencies(p);
		}		
		
		public long computeScoreBasedOnInconsistencies(PairScore p) 
		{	
			if(p.getQ().isAccept()==false && p.getR().isAccept()==false)
				return 0;
			if(p.getQ().isAccept()!=p.getR().isAccept())
				return -1;
			List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
			int genscore = coregraph.pairscores.computePairCompatibilityScore_general(p, null, verticesToMerge);
			if(genscore < 0)
				return -1;


	
			boolean askqueries = true;
			if(CheckInconsistecy)
			{
				LearnerGraph merged = MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(coregraph, verticesToMerge);
				long currentInconsistency = MarkovClassifier.computeInconsistencyOfAMerger(coregraph, verticesToMerge, inconsistenciesPerVertex, merged, Markov, cl, checker);
//				System.out.println("currentInconsistency"+currentInconsistency+" genscore= "+genscore);
				if (currentInconsistency > genscore )
					askqueries=true;
				else
					askqueries=false;
					
				
			}
			if (askqueries)
			{							
				//Generating Queries 			
				ArrayList<LearnerGraph>graphs=new ArrayList<LearnerGraph>();
				graphs.add(coregraph);

				assert coregraph.getStateNumber()==this.getTentativeAutomaton().getStateNumber();
				List<List<Label>> QuestionsFor = new ArrayList <List<Label>>();	
				if(CheckInconsistecy)
					cl=new MarkovClassifier(Markov,coregraph);
				
				if(option==1) // based on Core
				{			
					QuestionsFor = new ArrayList <List<Label>>();
				    LearnerGraph mergedcoregraph = MergeStates.mergeAndDeterminize_general(coregraph, p);
					QuestionsFor.addAll(ComputeQuestions.computeQS(p, coregraph, mergedcoregraph,null));
					QuestionsFor.addAll(MarkovQuestionGeneration.computeOneStep(p, coregraph, coregraph, false));
				}


				//check queries that has not answered
				for(List<Label> question:QuestionsFor)
				{
					if (GlobalConfiguration.getConfiguration().isAssertEnabled())
						for(LearnerGraph gr:graphs)
						{								
							if (gr.paths.getVertex(question)!=null)
							{
								throw new IllegalArgumentException("question "+ question+ " has already been answered");
							}
						}
				}
				
				// answering Queries 
			    if(QuestionsFor!=null && QuestionsFor.size() > 0) 
			    {
					Iterator<List<Label>> questionIt = QuestionsFor.iterator();	
					while(questionIt.hasNext())
					{
		    			List<Label> question = questionIt.next();
		    			Pair<Integer,String> answer = null;
		    			assert question!=null;	
		    			for(LearnerGraph graph:graphs)		    				
						if(graph.paths.getVertex(question)==null)  // there is no question path from the root to an existing state
						{
							answer = new Pair<Integer,String>(refgraph.paths.tracePathPrefixClosed(question, refgraph.getInit()),null);
							if(answer.firstElem != AbstractOracle.USER_ACCEPTED) // if it is answered as NO
							{
								LinkedList<Label> subAnswer = new LinkedList<Label>();
								subAnswer.addAll(question.subList(0, answer.firstElem + 1));
								if(!negatives.contains(subAnswer))
									NumberOfMarkovQuestions++;
								

							}

							// if query answered as positive
							if (answer.firstElem == AbstractOracle.USER_ACCEPTED) 
							{
								synchronized (AbstractLearnerGraph.syncObj) 
								{
									for(LearnerGraph gr:graphs)
									{
										// addd the answer to the PTA for further mergers
									    if (gr.getVertex(question) != null)
									    	throw new IllegalArgumentException("query "+question+" already answered, "+gr.getVertex(question));
										questioncoregraph.paths.augmentPTA(question, true, false, null);
										NumberOfMarkovQuestions++;
										questioncoregraphonly.paths.augmentPTA(question, true, false, null);
										gr.paths.augmentPTA(question, true, false, null);
									}
								}										
							}
						 
							// if query answered as negative
							else if (answer.firstElem >= 0) 
							{
								synchronized (AbstractLearnerGraph.syncObj) 
								{
									for(LearnerGraph gr:graphs)
									{
										LinkedList<Label> subAnswer = new LinkedList<Label>();
										subAnswer.addAll(question.subList(0, answer.firstElem + 1));
//										if (gr.getVertex(subAnswer) != null)
//											throw new IllegalArgumentException("query "+subAnswer+" already answered, "+gr.getVertex(subAnswer));
										negatives.add(subAnswer);
										if (gr.getVertex(subAnswer) == null) // if the path is not exsit add them
											gr.paths.augmentPTA(subAnswer, false, false, null);
										questioncoregraph.paths.augmentPTA(subAnswer, false, false, null);
//										NumberOfMarkovQuestions++;										
										questioncoregraphonly.paths.augmentPTA(subAnswer, false, false, null);										
									}									
								}				
							}							
							else
								throw new IllegalArgumentException("unexpected user choice "+answer);
						}
						if(CheckInconsistecy)
						{
							//updating Markov
							new MarkovClassifier(Markov,questioncoregraphonly).updateMarkov(true);
//							System.out.println(Markov.computePredictionMatrix());
						}

						verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						if(coregraph.pairscores.computePairCompatibilityScore_general(p, null, verticesToMerge) < 0)
							return -1;	
					
						
					}
			    }
			}

			
			verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
			return coregraph.pairscores.computePairCompatibilityScore_general(p, null, verticesToMerge);
		}

		/** This one returns a set of transitions in all directions. */
		@Override
		public Collection<Entry<Label, CmpVertex>> getSurroundingTransitions(CmpVertex currentRed) 
		{
			inverseGraph = (LearnerGraphND)MarkovClassifier.computeInverseGraph(coregraph,true);
			return	MarkovPassivePairSelection.obtainSurroundingTransitions(coregraph,inverseGraph,currentRed);
		}

		
		protected MarkovModel Markov;
		protected ConsistencyChecker checker;
		
		private static LearnerEvaluationConfiguration constructConfiguration(LearnerEvaluationConfiguration evalCnf, int threshold)
		{
			Configuration config = evalCnf.config.copy();
//			config.setRejectPositivePairsWithScoresLessThan(threshold);
			config.setGeneralisationThreshold(threshold);
			LearnerEvaluationConfiguration copy = new LearnerEvaluationConfiguration(config);
			copy.graph = evalCnf.graph;copy.testSet = evalCnf.testSet;
			copy.setLabelConverter(evalCnf.getLabelConverter());
			copy.ifthenSequences = evalCnf.ifthenSequences;copy.labelDetails=evalCnf.labelDetails;
			return copy;
		}
		
		public void setMarkov(MarkovModel m) {
			Markov=m;
		}

		public void setChecker(ConsistencyChecker c) {
			checker=c;
		}

		public ModifiedQSM(LearnerEvaluationConfiguration evalCnf, final LearnerGraph argInitialPTA, int threshold) 
		{
			super(constructConfiguration(evalCnf,threshold),null, argInitialPTA);
		}

		@Override 
		public Stack<PairScore> ChooseStatePairs(LearnerGraph graph)
		{			
			Stack<PairScore> outcome = graph.pairscores.chooseStatePairs(this);			
			if (!outcome.isEmpty())
			{
				Stack<PairScore> pairsWithScoresComputedUsingGeneralMerger = outcome;		
				PairScore chosenPair = null;
				chosenPair = pickPairQSMLike(pairsWithScoresComputedUsingGeneralMerger);
				outcome.clear();outcome.push(chosenPair);
			}
			return outcome;
		}	
		
		

		/** Used to sort the collection of pairs and scores and do the filtering if needed. 
		 * @param pairsAndScores */
		public Stack<PairScore>  ReturnSortedPairsAndScoresStackFromUnsorted(ArrayList<PairScore> pairsAndScores)
		{
			Stack<PairScore> result = new Stack<PairScore>();

			Collections.sort(pairsAndScores);// there is no point maintaining a sorted collection as we go since a single quicksort at the end will do the job
			if (coregraph.config.getPairsMergedPerHypothesis() > 0)
			{
				int numberOfElements = Math.min(coregraph.pairsAndScores.size(),coregraph.config.getPairsMergedPerHypothesis());
				result.addAll(pairsAndScores.subList(0, numberOfElements));
			}
			else result.addAll(pairsAndScores);

			return result;		
		}
		/*@Override 
		public LearnerGraph MergeAndDeterminize(LearnerGraph original, StatePair pair)
		{
			return MergeStates.mergeAndDeterminize(original, pair);
		}*/
		
		@Override
		public String toString()
		{
			return "EDSM_Markov";
		}
	}

	public static void main(String args[]) throws Exception
	{
		try
		{
		
			runExperiment(args);
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
		}
		finally
		{
			DrawGraphs.end();
		}
	}
	
	
	public static int runExperiment(String args[]) throws Exception
	{
		Configuration config = Configuration.getDefaultConfiguration().copy();
		config.setAskQuestions(false);
		config.setDebugMode(false);
		config.setGdLowToHighRatio(0.7);
		config.setRandomPathAttemptFudgeThreshold(1000);
		config.setTransitionMatrixImplType(STATETREE.STATETREE_LINKEDHASH);
		config.setLearnerScoreMode(ScoreMode.GENERAL);
		ConvertALabel converter = new Transform.InternStringLabel();					
//		config.setQuestionPathUnionLimit(1);
		GlobalConfiguration.getConfiguration().setProperty(G_PROPERTIES.LINEARWARNINGS, "false");

//		final int ThreadNumber = ExperimentRunner.getCpuNumber();	
//		ExecutorService executorService = Executors.newFixedThreadPool(ThreadNumber);
		final int minStateNumber =10;
		final int samplesPerFSM = 15;
		final int stateNumberIncrement = 10;
		final int rangeOfStateNumbers = 20+stateNumberIncrement;
		final int trainingSamplesPerFSM =5;
		
		final String branch = "OCT15;";
		RunSubExperiment<ThreadResult> experimentRunner = new RunSubExperiment<PairQualityLearner.ThreadResult>(ExperimentRunner.getCpuNumber(),"data",args);
		// Inference from a few traces
		final boolean onlyPositives=true;
		for(final int traceMultiplier: new int[]{6,10})
		for(final int chunkSize: new int[]{3})//0,1,2})
		for(final double traceLengthMultiplier: new double[]{0.125})//0,1,2})

		for(final double alphabetMultiplierMax:new double[]{0.5,1.0,2.0})
		{
			final AtomicLong comparisonsPerformed = new AtomicLong(0);
//			String selection = branch+"_"+"chunk="+chunkSize+";tracenum="+traceMultiplier+";tracelen="+traceLengthMultiplier+";statesMax="+(minStateNumber+rangeOfStateNumbers-stateNumberIncrement)+";alphabetMult="+alphabetMultiplierMax+";";
			String selection = branch+"_"+"chunk="+chunkSize+";tracenum="+traceMultiplier+";tracelen="+traceLengthMultiplier+";alphaMult="+alphabetMultiplierMax+";";

//		    final RBoxPlotCvs<Double> modfiedQSMQueries = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsmodfiedQSMQueries_"+selection+".csv"));
//		    final RBoxPlotCvs<Double> markovQSMQueries = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsmarkovQSMQueries_"+selection+".csv"));
//		    final RBoxPlotCvs<Double> QSMQueries = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsQSM_"+selection+".csv"));
		    
		    final RBoxPlotCvs<Double> modifiedQSMMQQueries = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsmodfiedQSMMQQueries_"+selection+".csv"));
		    final RBoxPlotCvs<Double> markovQSMMQQueries = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsmarkovQSMMQQueries_"+selection+".csv"));
		    final RBoxPlotCvs<Double> QSMMQQueries = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsQSM_MQQueries_"+selection+".csv"));
		    
			final RWilcoxon <String>  WilcoxonModifiedqsmVSqsmMQQueries=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_ModifiedqsmVSqsmMQQueries.csv"));
		    final RWilcoxon <String>  WilcoxonMarkovqsmVsqsmMQQueries=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_MarkovqsmVsqsmMQQueries.csv"));
		    final RWilcoxon <String>  WilcoxonMarkovqsmVsmodifiedqsmMQQueries=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_MarkovqsmVsmodifiedqsmMQQueries.csv"));

		    final RBoxPlotCvs<Double> modifiedQSMBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsmodifiedQSMBCR_"+selection+".csv"));
		    final RBoxPlotCvs<Double> markovQSMBCR= new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsmarkovQSMBCR_"+selection+".csv"));
		    final RBoxPlotCvs<Double> QSMBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsQSMBCR_"+selection+".csv"));
		    
		    final RWilcoxon <String>  WilcoxonModifiedqsmVSqsmBCR=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_ModifiedqsmVSqsmBCR.csv"));
			final RWilcoxon <String>  WilcoxonMarkovqsmVsqsmBCR=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_MarkovqsmVsqsmBCR.csv"));
		    final RWilcoxon <String>  WilcoxonMarkovqsmVsmodifiedqsmBCR=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_MarkovqsmVsmodifiedqsmBCR.csv"));
		  		    
		    final RBoxPlotCvs<Double> modifiedQSMDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsmodifiedQSMDiff_"+selection+".csv"));
		    final RBoxPlotCvs<Double> markovQSMDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsmarkovQSMDiff_"+selection+".csv"));
		    final RBoxPlotCvs<Double> QSMDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsQSMDiff_"+selection+".csv"));

		    final RWilcoxon <String>  WilcoxonModifiedqsmVSqsmDiff=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_ModifiedqsmVSqsmDiff.csv"));
		    final RWilcoxon <String>  WilcoxonMarkovqsmVsqsmDiff=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_MarkovqsmVsqsmDiff.csv"));
		    final RWilcoxon <String>  WilcoxonMarkovqsmVsmodifiedqsmDiff=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File(branch+"_"+selection +"_Wilcoxon_t_MarkovqsmVsmodifiedqsmDiff.csv"));

		    final RBoxPlotCvs<Double> gr_TransitionCoverageForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionstransitionCover_"+selection+".csv"));
			final RBoxPlotCvs<Double> MarkovPrecisionForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovPrecision2_"+selection+".csv"));
		    final RBoxPlotCvs<Double> MarkovRecallForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovRecall2_"+selection+".csv"));
		    final RBoxPlotCvs<Double> MarkovInconsistecies = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsInconsisitecies2_"+selection+".csv"));
		    
		    for(int states=minStateNumber;states < minStateNumber+rangeOfStateNumbers;states+=stateNumberIncrement)
			{

				final int traceQuantity = (int) (traceMultiplier);

				final int traceQuantityToUse = traceQuantity;
				
				// in order to compute the statistical test for each group of states, we generate a lot of object to add the mean of BCR and structural difference				
					for(int sample=0;sample<samplesPerFSM;++sample)
						for(int rndSelector=0;rndSelector<trainingSamplesPerFSM;++rndSelector)
						{
							LearnerRunner learnerRunner = new LearnerRunner(states,sample,rndSelector,experimentRunner.getTaskID(),traceQuantityToUse, config, converter);
							learnerRunner.setOnlyUsePositives(onlyPositives);
							learnerRunner.setAlphabetMultiplier(alphabetMultiplierMax);
							learnerRunner.setTracesAlphabetMultiplier(alphabetMultiplierMax);
							learnerRunner.setTraceLengthMultiplier(traceLengthMultiplier);
							learnerRunner.setChunkLen(chunkSize);
//							learnerRunner.setChunkLen(chunkLength);
							learnerRunner.setSelectionID(selection);
							learnerRunner.setPresetLearningParameters(0);
							learnerRunner.setDisableInconsistenciesInMergers(false);
							experimentRunner.submitTask(learnerRunner);
						}
				experimentRunner.collectOutcomeOfExperiments(new processSubExperimentResult<PairQualityLearner.ThreadResult>() {

					@Override
					public void processSubResult(ThreadResult result, RunSubExperiment<ThreadResult> experimentrunner) throws IOException 
					{// in these experiments, samples are singleton sequences because we run each of them in a separate process, in order to increase the efficiency with which all tasks are split between CPUs in an iceberg grid.					
						for(SampleData sample:result.samples)
						{					
//							experimentrunner.Record(modfiedQSMQueries,sample.modifiedQSM.numerofstates,sample.modifiedQSM.numberofQuestions,"green",null);
//							experimentrunner.Record(markovQSMQueries,sample.markovQSM.numerofstates,sample.markovQSM.numberofQuestions,"green",null);
//							experimentrunner.Record(QSMQueries,sample.referenceLearner.numerofstates,sample.referenceLearner.numberofQuestions,"blue",null);
							
							experimentrunner.Record(modifiedQSMMQQueries,sample.modifiedQSM.numerofstates,sample.modifiedQSM.numberofMQ,"green",null);
							experimentrunner.Record(markovQSMMQQueries,sample.markovQSM.numerofstates,sample.markovQSM.numberofMQ,"green",null);
							experimentrunner.Record(QSMMQQueries,sample.referenceLearner.numerofstates,sample.referenceLearner.numberofMQ,"blue",null);

							experimentrunner.Record(modifiedQSMBCR,sample.modifiedQSM.numerofstates,sample.modifiedQSM.differenceBCR.getValue(),"blue",null);
							experimentrunner.Record(markovQSMBCR,sample.markovQSM.numerofstates,sample.markovQSM.differenceBCR.getValue(),"blue",null);
							experimentrunner.Record(QSMBCR,sample.referenceLearner.numerofstates,sample.referenceLearner.differenceBCR.getValue(),"blue",null);

							experimentrunner.Record(WilcoxonModifiedqsmVSqsmBCR,  sample.modifiedQSM.differenceBCR.getValue(), sample.referenceLearner.differenceBCR.getValue(), null, null);
							experimentrunner.Record(WilcoxonMarkovqsmVsqsmBCR,  sample.markovQSM.differenceBCR.getValue(), sample.referenceLearner.differenceBCR.getValue(), null, null);
							experimentrunner.Record(WilcoxonMarkovqsmVsmodifiedqsmBCR,  sample.markovQSM.differenceBCR.getValue(), sample.modifiedQSM.differenceBCR.getValue(), null, null);

							experimentrunner.Record(WilcoxonMarkovqsmVsqsmMQQueries,  sample.markovQSM.numberofMQ, sample.referenceLearner.numberofMQ, null, null);
							experimentrunner.Record(WilcoxonModifiedqsmVSqsmMQQueries,  sample.modifiedQSM.numberofMQ, sample.referenceLearner.numberofMQ, null, null);
							experimentrunner.Record(WilcoxonMarkovqsmVsmodifiedqsmMQQueries,  sample.markovQSM.numberofMQ, sample.modifiedQSM.numberofMQ, null, null);

							experimentrunner.Record(modifiedQSMDiff,sample.modifiedQSM.numerofstates,sample.modifiedQSM.differenceStructural.getValue(),"blue",null);
							experimentrunner.Record(markovQSMDiff,sample.markovQSM.numerofstates,sample.markovQSM.differenceStructural.getValue(),"blue",null);
							experimentrunner.Record(QSMDiff,sample.referenceLearner.numerofstates,sample.referenceLearner.differenceStructural.getValue(),"blue",null);

							experimentrunner.Record(WilcoxonModifiedqsmVSqsmDiff,  sample.modifiedQSM.differenceStructural.getValue(), sample.referenceLearner.differenceStructural.getValue(), null, null);
							experimentrunner.Record(WilcoxonMarkovqsmVsqsmDiff,  sample.markovQSM.differenceStructural.getValue(), sample.referenceLearner.differenceStructural.getValue(), null, null);
							experimentrunner.Record(WilcoxonMarkovqsmVsmodifiedqsmDiff,  sample.markovQSM.differenceStructural.getValue(), sample.modifiedQSM.differenceStructural.getValue(), null, null);
						
							experimentrunner.Record(gr_TransitionCoverageForDifferentLengthOfTraces,Double.valueOf(sample.referenceLearner.numerofstates),(double)sample.transitionsSampled,null,null);
							experimentrunner.Record(MarkovRecallForDifferentLengthOfTraces,Double.valueOf(sample.stateNumber),(double)sample.markovRecall,null,null);
							experimentrunner.Record(MarkovPrecisionForDifferentLengthOfTraces,Double.valueOf(sample.stateNumber),(double)sample.markovPrecision,null,null);
							experimentrunner.Record(MarkovInconsistecies,Double.valueOf(sample.stateNumber),(double)sample.referenceinconsistency,null,null);
						}
					}
				
					@Override
					public String getSubExperimentName()
					{
						return "running tasks for learning whole graphs, preset "+chunkSize;
					}
					
					@SuppressWarnings("rawtypes")
					@Override
					public RGraph[] getGraphs() {
						return new RGraph[]{MarkovInconsistecies,MarkovPrecisionForDifferentLengthOfTraces,MarkovRecallForDifferentLengthOfTraces,gr_TransitionCoverageForDifferentLengthOfTraces,modifiedQSMMQQueries,markovQSMMQQueries,QSMMQQueries,WilcoxonModifiedqsmVSqsmMQQueries,WilcoxonMarkovqsmVsqsmMQQueries,WilcoxonMarkovqsmVsmodifiedqsmMQQueries,modifiedQSMBCR,markovQSMBCR,QSMBCR,WilcoxonModifiedqsmVSqsmBCR,WilcoxonMarkovqsmVsqsmBCR,WilcoxonMarkovqsmVsmodifiedqsmBCR,modifiedQSMDiff,markovQSMDiff,QSMDiff,WilcoxonModifiedqsmVSqsmDiff,WilcoxonMarkovqsmVsqsmDiff,WilcoxonMarkovqsmVsmodifiedqsmDiff};

					}
					
				});
				

				if (experimentRunner.isInteractive())
					System.out.println("\nLOG of comparisons performed: "+Math.log10(comparisonsPerformed.doubleValue())+"\n");
			}	  
		}	
		return experimentRunner.successfulTermination();
	}

}