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
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Stack;
import java.util.concurrent.Callable;







import java.util.concurrent.atomic.AtomicLong;

import edu.uci.ics.jung.graph.impl.DirectedSparseGraph;
import statechum.Configuration;
import statechum.Configuration.STATETREE;
import statechum.Configuration.ScoreMode;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.DeterministicDirectedSparseGraph.VertID;
import statechum.GlobalConfiguration;
import statechum.GlobalConfiguration.G_PROPERTIES;
import statechum.JUConstants;
import statechum.Label;
import statechum.analysis.learning.DrawGraphs;
import statechum.analysis.learning.DrawGraphs.RBoxPlot;
import statechum.analysis.learning.DrawGraphs.RBoxPlotCvs;
import statechum.analysis.learning.DrawGraphs.RGraph;
import statechum.analysis.learning.DrawGraphs.RWilcoxon;
import statechum.analysis.learning.DrawGraphs.SquareBagPlot;
import statechum.analysis.learning.DrawGraphs.Wilcoxon;
import statechum.analysis.learning.MarkovClassifier;
import statechum.analysis.learning.MarkovClassifier.ConsistencyChecker;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.PrecisionRecall.ConfusionMatrix;
import statechum.analysis.learning.MarkovModel;
import statechum.analysis.learning.PairScore;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.experiments.ExperimentRunner;
import statechum.analysis.learning.experiments.PaperUAS;
import statechum.analysis.learning.experiments.SGE_ExperimentRunner.RunSubExperiment;
import statechum.analysis.learning.experiments.SGE_ExperimentRunner.processSubExperimentResult;
import statechum.analysis.learning.experiments.PairSelection.Cav2014.KTailsReferenceLearner;
import statechum.analysis.learning.experiments.PairSelection.LearnFromTracesUsingExperimentalLearners.TraceLoader;
import statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.LearnerThatCanClassifyPairs;
import statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.SampleData;
import statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.ThreadResult;
import statechum.analysis.learning.experiments.mutation.DiffExperiments;
import statechum.analysis.learning.linear.GD;
import statechum.analysis.learning.observers.ProgressDecorator.LearnerEvaluationConfiguration;
import statechum.analysis.learning.rpnicore.AMEquivalenceClass;
import statechum.analysis.learning.rpnicore.AbstractLearnerGraph;
import statechum.analysis.learning.rpnicore.AbstractPathRoutines;
import statechum.analysis.learning.rpnicore.AbstractPersistence;
import statechum.analysis.learning.rpnicore.FsmParser;
import statechum.analysis.learning.rpnicore.LearnerGraph;
import statechum.analysis.learning.rpnicore.LearnerGraphCachedData;
import statechum.analysis.learning.rpnicore.LearnerGraphND;
import statechum.analysis.learning.rpnicore.LearnerGraphNDCachedData;
import statechum.analysis.learning.rpnicore.MergeStates;
import statechum.analysis.learning.rpnicore.PairScoreComputation;
import statechum.analysis.learning.rpnicore.RandomPathGenerator;
import statechum.analysis.learning.rpnicore.RandomPathGenerator.RandomLengthGenerator;
import statechum.analysis.learning.rpnicore.Transform;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;
import statechum.analysis.learning.rpnicore.WMethod;
import statechum.model.testset.PTASequenceEngine.FilterPredicate;
import statechum.collections.ArrayMapWithSearch;
import statechum.collections.ArrayMapWithSearchPos;
import statechum.collections.HashMapWithSearch;


public class FinalPassiveCaseStudy extends PairQualityLearner
{
	public static class LearnerRunner implements Callable<ThreadResult>
	{
		protected final Configuration config;
		protected final ConvertALabel converter;
		protected final int sample=0;
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
		
		public LearnerRunner(int argSeed, Configuration conf, ConvertALabel conv)
		{
			config = conf;seed = argSeed;converter=conv;
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
				setlearningParameters(true, false, false, false, true);break;
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
			if (tracesAlphabetMultiplier <= 0)
				tracesAlphabetMultiplier = alphabetMultiplier;

			ThreadResult outcome = new ThreadResult();

			LearnerEvaluationConfiguration learnerEval = new LearnerEvaluationConfiguration(config);learnerEval.setLabelConverter(converter);			

//			LearnerGraph referenceGraphAsText = FsmParser.buildLearnerGraph("q0-critical->q1-notcritical->q0\nq1-highwater->q3-notcritical->q2\nq0-highwater->q2-switchon->q4-turnon->q5-critical->q6-switchoff->q8-turnoff->q3\nq5-lowwater->q7-switchoff->q9-turnoff->q0","specgraph",config,converter);
//			LearnerGraph referenceGraphAsText = FsmParser.buildLearnerGraph("q1-CONNECT!->q2-VERSION?->q3\nq2-VERSION!->q4\nq3-VERSION!->q5\nq4-VERSION?->q5-KEXINIT!->q6\nq5-KEXINIT?->q7\nq6-KEXINIT?->q8\nq7-KEXINIT!->q8-KEXDH_INIT!->q9-KEXDH_REPLY?->q10\nq6-KEXDH_INIT!->q11-KEXINIT?->q9\nq10-NEWKEYS?->q13\nq10-NEWKEYS!->q14\nq13-NEWKEYS!->q5\nq14-NEWKEYS?->q5", "specgraph",config,converter);
			LearnerGraph referenceGraphAsText = FsmParser.buildLearnerGraph("q1-initialise->q2-connect->q3-login->q4-storefile->q14\nq4-changedir->q5\nq4-listfiles->q6\nq4-makedir->q7\nq4-setfiletype->q8\nq5-listnames->q9\nq6-retrievefile->q6-changedir->q10\nq6-logout->q15\nq7-makedir->q7-logout->q15\nq8-rename->q12\nq8-storefile->q11\nq9-delete->q9-appendfile->q14\nq10-listfiles->q6\nq11-appendfile->q13\nq12-storefile->q13\nq12-logout->q15\nq13-logout->q15\nq13-setfiletype->q8\nq14-logout->q15-disconnect->q1\nq9-changedir->q5", "specgraph",config,converter);
//			LearnerGraph referenceGraphAsText = FsmParser.buildLearnerGraph("q0-open->q1-opendoors->q3-close->q5-closedoors->q0-start->q2-startmotor->q4-stop->q7-stopmotor->q0\nq6-highspeed->q9-lowspeed->q6-stop->q10-stopmotor->q13-start->q15-startmotor->q6\nq4-leavingstation->q6\nq9-approachingstation->q12-lowspeed->q8\nq6-approachingstation->q8-atstation->q4\nq8-stop->q11-stopmotor->q14-start->q16-startmotor->q8", "specgraph",config,converter);
			
			LearnerGraph referenceGraph = new LearnerGraph(config);AbstractPathRoutines.convertToNumerical(referenceGraphAsText,referenceGraph);
			final int states = referenceGraph.getStateNumber(), alphabet = referenceGraph.pathroutines.computeAlphabet().size();
			//Visualiser.updateFrame(referenceGraph, null);

			final Collection<List<Label>> testSet = PaperUAS.computeEvaluationSet(referenceGraph,states*3,makeEven(states*states*2));
			testSet.addAll(referenceGraph.wmethod.computeNewTestSet(2));

//			System.out.println(testSet.size());

//			System.out.println("states= "+states);
//			System.out.println("alphabet= "+alphabet);

			for(int attempt=0;attempt<30;++attempt)
			{// try learning the same machine a few times
				final int tracesAlphabet = (int)(tracesAlphabetMultiplier*states);

 				LearnerGraph pta = new LearnerGraph(config);
				RandomPathGenerator generator = new RandomPathGenerator(referenceGraph,new Random(attempt),5,null);
				final int tracesToGenerate = makeEven(traceQuantity);

				generator.generateRandomPosNeg(tracesToGenerate, 1, false, new RandomLengthGenerator() {
										
						@Override
						public int getLength() {
//							System.out.println((traceLengthMultiplier*states*tracesAlphabet));
							return (int)(traceLengthMultiplier*states*alphabet);
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

			

				pta.clearColours();

				if (!onlyUsePositives)
					assert pta.getStateNumber() > pta.getAcceptStateNumber() : "graph with only accept states but onlyUsePositives is not set";
				else 
					assert pta.getStateNumber() == pta.getAcceptStateNumber() : "graph with negatives but onlyUsePositives is set";
					
				LearnerGraph trimmedReference = MarkovPassivePairSelection.trimUncoveredTransitions(pta,referenceGraph);
				SampleData dataSample = new SampleData(null,null);
				final Configuration deepCopy = pta.config.copy();deepCopy.setLearnerCloneGraph(true);
				LearnerGraph ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
			
				{
					LearnerGraph ptaToUseForInference = new LearnerGraph(deepCopy);
					LearnerGraph.copyGraphs(pta, ptaToUseForInference);
					assert ptaToUseForInference.getStateNumber() == pta.getStateNumber();
					final MarkovModel m= new MarkovModel(3,true,true, disableInconsistenciesInMergers);
					new MarkovClassifier(m, pta).updateMarkov(false);// construct Markov chain if asked for.
					EDSM_MarkovLearner learnerOfPairs = null;
					LearnerGraph actualAutomaton = null;
					
					final ConsistencyChecker checker = new MarkovClassifier.DifferentPredictionsInconsistencyNoBlacklistingIncludeMissingPrefixes();
					long inconsistencyForTheReferenceGraph = MarkovClassifier.computeInconsistency(referenceGraph, m, checker,false);
					Collection<Set<CmpVertex>> verticesToMergeBasedOnInitialPTA=null;
								
				
					if (useCentreVertex)
					{
						final MarkovClassifier ptaClassifier = new MarkovClassifier(m,pta);
						final List<List<Label>> pathsToMerge=ptaClassifier.identifyPathsToMerge(checker);
						// These vertices are merged first and then the learning start from the root as normal.
						// The reason to learn from the root is a memory cost. if we learn from the middle, we can get a better results
						verticesToMergeBasedOnInitialPTA=ptaClassifier.buildVerticesToMergeForPaths(pathsToMerge);
	
						List<StatePair> pairsListInitialMerge = ptaClassifier.buildVerticesToMergeForPath(pathsToMerge);
						LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMergeInitialMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						int scoreInitialMerge = pta.pairscores.computePairCompatibilityScore_general(null, pairsListInitialMerge, verticesToMergeInitialMerge);
						assert scoreInitialMerge >= 0;
						ptaToUseForInference = MergeStates.mergeCollectionOfVertices(pta, null, verticesToMergeInitialMerge);
						final CmpVertex vertexWithMostTransitions = MarkovPassivePairSelection.findVertexWithMostTransitions(ptaToUseForInference,MarkovClassifier.computeInverseGraph(pta));
						if (useMostConnectedVertexToStartLearning)
						{
							ptaToUseForInference.clearColours();ptaToUseForInference.getInit().setColour(null);vertexWithMostTransitions.setColour(JUConstants.RED);
						}
						LearnerGraphND inverseOfPtaAfterInitialMerge = MarkovClassifier.computeInverseGraph(ptaToUseForInference);
						System.out.println("Centre vertex: "+vertexWithMostTransitions+" number of transitions: "+MarkovPassivePairSelection.countTransitions(ptaToUseForInference, inverseOfPtaAfterInitialMerge, vertexWithMostTransitions));
					}

					learnerOfPairs = new EDSM_MarkovLearner(learnerEval,ptaToUseForInference,referenceGraph,0);learnerOfPairs.setMarkov(m);learnerOfPairs.setChecker(checker);
					learnerOfPairs.setUseNewScoreNearRoot(useDifferentScoringNearRoot);learnerOfPairs.setUseClassifyPairs(useClassifyToOrderPairs);
					learnerOfPairs.setDisableInconsistenciesInMergers(disableInconsistenciesInMergers);

					actualAutomaton = learnerOfPairs.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					actualAutomaton.setName("CVS");

				
					if (verticesToMergeBasedOnInitialPTA != null && mergeIdentifiedPathsAfterInference)
					{
						LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						int genScore = actualAutomaton.pairscores.computePairCompatibilityScore_general(null, constructPairsToMergeBasedOnSetsToMerge(actualAutomaton.transitionMatrix.keySet(),verticesToMergeBasedOnInitialPTA), verticesToMerge);
						assert genScore >= 0;
						actualAutomaton = MergeStates.mergeCollectionOfVertices(actualAutomaton, null, verticesToMerge);
					}			
				
					//dataSample.difference = new DifferenceToReferenceDiff(0, 0);
					//dataSample.differenceForReferenceLearner = new DifferenceToReferenceDiff(0, 0);
					long inconsistencyActual = MarkovClassifier.computeInconsistency(actualAutomaton, m, checker,false);
					
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
					System.out.println("EDSM-Markov3");
					
					dataSample.EDSMMarkovKthree = estimateDifference(referenceGraph,actualAutomaton,testSet);
					dataSample.EDSMMarkovKthree.inconsistency = inconsistencyForTheReferenceGraph;
					dataSample.referenceLearner = zeroScore;
					dataSample.EDSMMarkovKthree.numerofstates=referenceGraph.getStateNumber();
					statechum.Pair<Double,Double> correctnessOfMarkov = new MarkovClassifier(m, referenceGraph).evaluateCorrectnessOfMarkov();
					dataSample.EDSMMarkovKthree.markovPrecision = Math.round(100*correctnessOfMarkov.firstElem);
					dataSample.EDSMMarkovKthree.markovRecall = Math.round(100*correctnessOfMarkov.secondElem);
					dataSample.miscGraphs = new TreeMap<String,ScoresForGraph>();
					dataSample.miscGraphs.put("E-M",dataSample.EDSMMarkovKthree);
				}
				
				//EDSM-Markov 2

				{
					LearnerGraph ptaToUseForInference = new LearnerGraph(deepCopy);
					LearnerGraph.copyGraphs(pta, ptaToUseForInference);
					assert ptaToUseForInference.getStateNumber() == pta.getStateNumber();
					final MarkovModel m2= new MarkovModel(2,true,true, disableInconsistenciesInMergers);
					new MarkovClassifier(m2, pta).updateMarkov(false);// construct Markov chain if asked for.
					EDSM_MarkovLearner learnerOfPairs = null;
					LearnerGraph actualAutomaton1 = null;
					
					final ConsistencyChecker checker = new MarkovClassifier.DifferentPredictionsInconsistencyNoBlacklistingIncludeMissingPrefixes();
					long inconsistencyForTheReferenceGraph = MarkovClassifier.computeInconsistency(referenceGraph, m2, checker,false);
					Collection<Set<CmpVertex>> verticesToMergeBasedOnInitialPTA=null;
								
				
					if (useCentreVertex)
					{
						final MarkovClassifier ptaClassifier = new MarkovClassifier(m2,pta);
						final List<List<Label>> pathsToMerge=ptaClassifier.identifyPathsToMerge(checker);
						// These vertices are merged first and then the learning start from the root as normal.
						// The reason to learn from the root is a memory cost. if we learn from the middle, we can get a better results
						verticesToMergeBasedOnInitialPTA=ptaClassifier.buildVerticesToMergeForPaths(pathsToMerge);
	
						List<StatePair> pairsListInitialMerge = ptaClassifier.buildVerticesToMergeForPath(pathsToMerge);
						LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMergeInitialMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						int scoreInitialMerge = pta.pairscores.computePairCompatibilityScore_general(null, pairsListInitialMerge, verticesToMergeInitialMerge);
						assert scoreInitialMerge >= 0;
						ptaToUseForInference = MergeStates.mergeCollectionOfVertices(pta, null, verticesToMergeInitialMerge);
						final CmpVertex vertexWithMostTransitions = MarkovPassivePairSelection.findVertexWithMostTransitions(ptaToUseForInference,MarkovClassifier.computeInverseGraph(pta));
						if (useMostConnectedVertexToStartLearning)
						{
							ptaToUseForInference.clearColours();ptaToUseForInference.getInit().setColour(null);vertexWithMostTransitions.setColour(JUConstants.RED);
						}
						LearnerGraphND inverseOfPtaAfterInitialMerge = MarkovClassifier.computeInverseGraph(ptaToUseForInference);
						System.out.println("Centre vertex: "+vertexWithMostTransitions+" number of transitions: "+MarkovPassivePairSelection.countTransitions(ptaToUseForInference, inverseOfPtaAfterInitialMerge, vertexWithMostTransitions));
					}

					learnerOfPairs = new EDSM_MarkovLearner(learnerEval,ptaToUseForInference,referenceGraph,0);learnerOfPairs.setMarkov(m2);learnerOfPairs.setChecker(checker);
					learnerOfPairs.setUseNewScoreNearRoot(useDifferentScoringNearRoot);learnerOfPairs.setUseClassifyPairs(useClassifyToOrderPairs);
					learnerOfPairs.setDisableInconsistenciesInMergers(disableInconsistenciesInMergers);

					actualAutomaton1 = learnerOfPairs.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					actualAutomaton1.setName("CVS");

				
					if (verticesToMergeBasedOnInitialPTA != null && mergeIdentifiedPathsAfterInference)
					{
						LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						int genScore = actualAutomaton1.pairscores.computePairCompatibilityScore_general(null, constructPairsToMergeBasedOnSetsToMerge(actualAutomaton1.transitionMatrix.keySet(),verticesToMergeBasedOnInitialPTA), verticesToMerge);
						assert genScore >= 0;
						actualAutomaton1 = MergeStates.mergeCollectionOfVertices(actualAutomaton1, null, verticesToMerge);
					}			
				
					System.out.println(actualAutomaton1.getStateNumber());
					//dataSample.difference = new DifferenceToReferenceDiff(0, 0);
					//dataSample.differenceForReferenceLearner = new DifferenceToReferenceDiff(0, 0);
					long inconsistencyActual = MarkovClassifier.computeInconsistency(actualAutomaton1, m2, checker,false);
					
					VertID rejectVertexID = null;
					for(CmpVertex v:actualAutomaton1.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = actualAutomaton1.nextID(false);
					actualAutomaton1.pathroutines.completeGraphPossiblyUsingExistingVertex(rejectVertexID);// we need to complete the graph, otherwise we are not matching it with the original one that has been completed.
					System.out.println("EDSM-Markov2");
					
//					GD<List<CmpVertex>,List<CmpVertex>,LearnerGraphNDCachedData,LearnerGraphNDCachedData> gd = 
//		                    new GD<List<CmpVertex>,List<CmpVertex>,LearnerGraphNDCachedData,LearnerGraphNDCachedData>();
//	                final AbstractLearnerGraph graph_Learnt = actualAutomaton1;
//	                final AbstractLearnerGraph graph1=referenceGraph;
//	                DirectedSparseGraph gr = gd.showGD(graph_Learnt,graph1,ExperimentRunner.getCpuNumber());
//	                 Visualiser.updateFrame(gr, referenceGraph);
//					referenceGraph.setName("a");
//	                 Visualiser.updateFrame(referenceGraph, null);

					dataSample.EDSMMarkovKtwo = estimateDifference(referenceGraph,actualAutomaton1,testSet);
					dataSample.EDSMMarkovKtwo.inconsistency = inconsistencyForTheReferenceGraph;
					dataSample.referenceLearner = zeroScore;
					dataSample.EDSMMarkovKtwo.numerofstates=referenceGraph.getStateNumber();
					statechum.Pair<Double,Double> correctnessOfMarkov = new MarkovClassifier(m2, referenceGraph).evaluateCorrectnessOfMarkov();
					dataSample.EDSMMarkovKtwo.markovPrecision = Math.round(100*correctnessOfMarkov.firstElem);
					dataSample.EDSMMarkovKtwo.markovRecall = Math.round(100*correctnessOfMarkov.secondElem);
					dataSample.miscGraphs = new TreeMap<String,ScoresForGraph>();
					dataSample.miscGraphs.put("E-M",dataSample.EDSMMarkovKtwo);
				}
				
				//EDSM-Markov 4
				
				{
					LearnerGraph ptaToUseForInference = new LearnerGraph(deepCopy);
					LearnerGraph.copyGraphs(pta, ptaToUseForInference);
					assert ptaToUseForInference.getStateNumber() == pta.getStateNumber();
					final MarkovModel m4= new MarkovModel(4,true,true, disableInconsistenciesInMergers);
					new MarkovClassifier(m4, pta).updateMarkov(false);// construct Markov chain if asked for.
					EDSM_MarkovLearner learnerOfPairs = null;
					LearnerGraph actualAutomaton4 = null;
					
					final ConsistencyChecker checker = new MarkovClassifier.DifferentPredictionsInconsistencyNoBlacklistingIncludeMissingPrefixes();
					long inconsistencyForTheReferenceGraph = MarkovClassifier.computeInconsistency(referenceGraph, m4, checker,false);
					Collection<Set<CmpVertex>> verticesToMergeBasedOnInitialPTA=null;
								
				
					if (useCentreVertex)
					{
						final MarkovClassifier ptaClassifier = new MarkovClassifier(m4,pta);
						final List<List<Label>> pathsToMerge=ptaClassifier.identifyPathsToMerge(checker);
						// These vertices are merged first and then the learning start from the root as normal.
						// The reason to learn from the root is a memory cost. if we learn from the middle, we can get a better results
						verticesToMergeBasedOnInitialPTA=ptaClassifier.buildVerticesToMergeForPaths(pathsToMerge);
	
						List<StatePair> pairsListInitialMerge = ptaClassifier.buildVerticesToMergeForPath(pathsToMerge);
						LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMergeInitialMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						int scoreInitialMerge = pta.pairscores.computePairCompatibilityScore_general(null, pairsListInitialMerge, verticesToMergeInitialMerge);
						assert scoreInitialMerge >= 0;
						ptaToUseForInference = MergeStates.mergeCollectionOfVertices(pta, null, verticesToMergeInitialMerge);
						final CmpVertex vertexWithMostTransitions = MarkovPassivePairSelection.findVertexWithMostTransitions(ptaToUseForInference,MarkovClassifier.computeInverseGraph(pta));
						if (useMostConnectedVertexToStartLearning)
						{
							ptaToUseForInference.clearColours();ptaToUseForInference.getInit().setColour(null);vertexWithMostTransitions.setColour(JUConstants.RED);
						}
						LearnerGraphND inverseOfPtaAfterInitialMerge = MarkovClassifier.computeInverseGraph(ptaToUseForInference);
						System.out.println("Centre vertex: "+vertexWithMostTransitions+" number of transitions: "+MarkovPassivePairSelection.countTransitions(ptaToUseForInference, inverseOfPtaAfterInitialMerge, vertexWithMostTransitions));
					}

					learnerOfPairs = new EDSM_MarkovLearner(learnerEval,ptaToUseForInference,referenceGraph,0);learnerOfPairs.setMarkov(m4);learnerOfPairs.setChecker(checker);
					learnerOfPairs.setUseNewScoreNearRoot(useDifferentScoringNearRoot);learnerOfPairs.setUseClassifyPairs(useClassifyToOrderPairs);
					learnerOfPairs.setDisableInconsistenciesInMergers(disableInconsistenciesInMergers);

					actualAutomaton4 = learnerOfPairs.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					actualAutomaton4.setName("CVS");

				
					if (verticesToMergeBasedOnInitialPTA != null && mergeIdentifiedPathsAfterInference)
					{
						LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
						int genScore = actualAutomaton4.pairscores.computePairCompatibilityScore_general(null, constructPairsToMergeBasedOnSetsToMerge(actualAutomaton4.transitionMatrix.keySet(),verticesToMergeBasedOnInitialPTA), verticesToMerge);
						assert genScore >= 0;
						actualAutomaton4 = MergeStates.mergeCollectionOfVertices(actualAutomaton4, null, verticesToMerge);
					}			
				
					//dataSample.difference = new DifferenceToReferenceDiff(0, 0);
					//dataSample.differenceForReferenceLearner = new DifferenceToReferenceDiff(0, 0);
					long inconsistencyActual = MarkovClassifier.computeInconsistency(actualAutomaton4, m4, checker,false);
					
					VertID rejectVertexID = null;
					for(CmpVertex v:actualAutomaton4.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = actualAutomaton4.nextID(false);
					actualAutomaton4.pathroutines.completeGraphPossiblyUsingExistingVertex(rejectVertexID);// we need to complete the graph, otherwise we are not matching it with the original one that has been completed.
					System.out.println("EDSM-Markov4");
					
					dataSample.EDSMMarkovKfour = estimateDifference(referenceGraph,actualAutomaton4,testSet);
					dataSample.EDSMMarkovKfour.inconsistency = inconsistencyForTheReferenceGraph;
					dataSample.referenceLearner = zeroScore;
					dataSample.EDSMMarkovKfour.numerofstates=referenceGraph.getStateNumber();
					statechum.Pair<Double,Double> correctnessOfMarkov = new MarkovClassifier(m4, referenceGraph).evaluateCorrectnessOfMarkov();
					dataSample.EDSMMarkovKfour.markovPrecision = Math.round(100*correctnessOfMarkov.firstElem);
					dataSample.EDSMMarkovKfour.markovRecall = Math.round(100*correctnessOfMarkov.secondElem);
					dataSample.miscGraphs = new TreeMap<String,ScoresForGraph>();
					dataSample.miscGraphs.put("E-M",dataSample.EDSMMarkovKfour);
				}
				
				
				// This is to ensure that scoring is computed in the usual way rather than with override.
				
				{
					Configuration evaluationConfig = config.copy();evaluationConfig.setLearnerScoreMode(ScoreMode.COMPATIBILITY);				
					LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);
					final Configuration deepCopy1 = pta.config.copy();deepCopy.setLearnerCloneGraph(true);
					LearnerGraph ptaCopy1 = new LearnerGraph(deepCopy1);LearnerGraph.copyGraphs(pta, ptaCopy1);
					assert ptaCopy1.getStateNumber() == pta.getStateNumber();

					try
					{
						LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
						outcomeOfReferenceLearner = new ReferenceLearner(referenceLearnerEval,referenceGraph,ptaCopy1,false).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
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
						System.out.println("Sicco's Reference");
//						Visualiser.updateFrame(outcomeOfReferenceLearner, null);
						dataSample.referenceLearner = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
//						dataSample.referenceLearner.inconsistency = MarkovClassifier.computeInconsistency(outcomeOfReferenceLearner, m, checker,false);
					}
					catch(Cav2014.LearnerAbortedException ex)
					{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					}
					dataSample.miscGraphs.put("S",dataSample.referenceLearner);

				}
				
				
				


				dataSample.traceNumber = traceQuantity;
				
			
				
				dataSample.fractionOfStatesIdentifiedBySingletons=Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph));
				dataSample.stateNumber = referenceGraph.getStateNumber();
				dataSample.transitionsSampled = Math.round(100*trimmedReference.pathroutines.countEdges()/referenceGraph.pathroutines.countEdges());
//				dataSample.comparisonsPerformed = learnerOfPairs.comparisonsPerformed;
//				Collection<List<Label>> wset=referenceGraph.wmethod.getFullTestSet(10);
				int wSeqLen=0;
//				for(List<Label> seq:wset)
//				{
//					int len = seq.size();if (len > wSeqLen) wSeqLen=len;
//				}
//				System.out.println("actual: "+actualAutomaton.getStateNumber()+" from reference learner: "+outcomeOfReferenceLearner.getStateNumber()+ 
//						" difference actual is "+dataSample.actualLearner.differenceBCR.getValue()+ " difference ref is "+dataSample.referenceLearner.differenceBCR.getValue()
//						+ " inconsistency learnt "+dataSample.actualLearner.inconsistency+" inconsistency reference: "+inconsistencyForTheReferenceGraph
//						+" transitions per state: "+(double)referenceGraph.pathroutines.countEdges()/referenceGraph.getStateNumber()+
//							" W seq max len "+wSeqLen+
////							" Uniquely identifiable by W "+Math.round(100*MarkovClassifier.calculateFractionOfIdentifiedStates(referenceGraph, wset))+" %"+
//						" and by singletons "+Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph))+" %"
//						);
				outcome.samples.add(dataSample);
			}

			return outcome;
		}

		// Delegates to a specific estimator
		ScoresForGraph estimateDifference(LearnerGraph reference, LearnerGraph actual,Collection<List<Label>> testSet)
		{
			ScoresForGraph outcome = new ScoresForGraph();
			outcome.differenceStructural=DifferenceToReferenceDiff.estimationOfDifferenceDiffMeasure(reference, actual, config, 1);
			outcome.differenceBCR=DifferenceToReferenceLanguageBCR.estimationOfDifference(reference, actual,testSet);
			System.out.println("Structure= "+outcome.differenceStructural.getValue());
			System.out.println("BCR= "+outcome.differenceBCR.getValue()+" details: "+outcome.differenceBCR.toString());
			System.out.println("---------------------------------------------------");

			return outcome;
		}			
	}
	
		
	public static Collection<StatePair> constructPairsToMergeBasedOnSetsToMerge(Set<CmpVertex> validStates, Collection<Set<CmpVertex>> verticesToMergeBasedOnInitialPTA)
	{
		List<StatePair> pairsList = new LinkedList<StatePair>();
		for(Set<CmpVertex> groupOfStates:verticesToMergeBasedOnInitialPTA)
		{
			Set<CmpVertex> validStatesInGroup = new TreeSet<CmpVertex>();validStatesInGroup.addAll(groupOfStates);validStatesInGroup.retainAll(validStates);
			if (validStatesInGroup.size() > 1)
			{
				CmpVertex v0=validStatesInGroup.iterator().next();
				for(CmpVertex v:validStatesInGroup)
				{
					if (v != v0)
						pairsList.add(new StatePair(v0,v));
					v0=v;
				}
			}
		}
		return pairsList;
	}
			
	public static final ScoresForGraph zeroScore;
	static
	{
		zeroScore = new ScoresForGraph();zeroScore.differenceBCR=new DifferenceToReferenceLanguageBCR(0, 0, 0, 0);zeroScore.differenceStructural=new DifferenceToReferenceDiff(0, 0);
	}

	/** Uses the supplied classifier to rank pairs. */
	public static class EDSM_MarkovLearner extends LearnerThatCanClassifyPairs implements statechum.analysis.learning.rpnicore.PairScoreComputation.RedNodeSelectionProcedure
	{
		@SuppressWarnings("unused")
		@Override
		public CmpVertex selectRedNode(LearnerGraph gr,Collection<CmpVertex> reds, Collection<CmpVertex> tentativeRedNodes) 
		{
			return tentativeRedNodes.iterator().next();
		}
		
		@SuppressWarnings("unused")
		@Override
		public CmpVertex resolvePotentialDeadEnd(LearnerGraph gr, Collection<CmpVertex> reds, List<PairScore> pairs) 
		{
			return null;												
		}
		
		long inconsistencyFromAnEarlierIteration = 0;
		LearnerGraph coregraph = null;
		LearnerGraph extendedGraph = null;
		MarkovClassifier cl=null;
		LearnerGraphND inverseGraph = null;
		long comparisonsPerformed = 0;
		
		boolean useNewScoreNearRoot = true, useClassifyPairs = true;

		public void setUseNewScoreNearRoot(boolean v)
		{
			useNewScoreNearRoot = v;
		}
		
		public void setUseClassifyPairs(boolean v)
		{
			useClassifyPairs = v;
		}
		
		Map<CmpVertex,Long> inconsistenciesPerVertex = null;
		Map<CmpVertex,Long> consistenciesPerVertex = null;

		/** Whether we should try learning with zero inconsistencies, to see how heuristics fare. */
		protected boolean disableInconsistenciesInMergers = false;
		
		public void setDisableInconsistenciesInMergers(boolean v)
		{
			disableInconsistenciesInMergers = v;
		}
		
		/*@Override 
		public LearnerGraph MergeAndDeterminize(LearnerGraph original, StatePair pair)
		{
			return MergeStates.mergeAndDeterminize(original, pair);
		}*/

		@Override
		public void initComputation(LearnerGraph graph) 
		{
			coregraph = graph;
					 				
			long value = MarkovClassifier.computeInconsistency(coregraph, Markov, checker,false);
			inconsistencyFromAnEarlierIteration=value;
			cl = new MarkovClassifier(Markov, coregraph);
//		    extendedGraph = cl.constructMarkovTentative();
			inverseGraph = (LearnerGraphND)MarkovClassifier.computeInverseGraph(coregraph,true);
			inconsistenciesPerVertex = new ArrayMapWithSearchPos<CmpVertex,Long>(coregraph.getStateNumber());

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
			++comparisonsPerformed;
			long currentInconsistency = 0;
			
			List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
			int genScore = coregraph.pairscores.computePairCompatibilityScore_general(p, null, verticesToMerge);
			if(genScore < 0)
				return -1;
			long score= genScore;
			if (genScore >= 0)
			{					
				LearnerGraph merged = MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(coregraph, verticesToMerge);
				currentInconsistency = MarkovClassifier.computeInconsistencyOfAMerger(coregraph, verticesToMerge, inconsistenciesPerVertex, merged, Markov, cl, checker);
				score=genScore-currentInconsistency;
			}

			return score;
		}

		/** This one returns a set of transitions in all directions. */
		@Override
		public Collection<Entry<Label, CmpVertex>> getSurroundingTransitions(CmpVertex currentRed) 
		{
			return	MarkovPassivePairSelection.obtainSurroundingTransitions(coregraph,inverseGraph,currentRed);
		}

		protected MarkovModel Markov;
		protected ConsistencyChecker checker;
		
		private static LearnerEvaluationConfiguration constructConfiguration(LearnerEvaluationConfiguration evalCnf, int threshold)
		{
			Configuration config = evalCnf.config.copy();config.setRejectPositivePairsWithScoresLessThan(threshold);
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

		public EDSM_MarkovLearner(LearnerEvaluationConfiguration evalCnf, final LearnerGraph argInitialPTA, final LearnerGraph reference, int threshold) 
		{
			super(constructConfiguration(evalCnf,threshold),reference, argInitialPTA);
		}

		@Override 
		public Stack<PairScore> ChooseStatePairs(LearnerGraph graph)
		{
			Stack<PairScore> outcome = graph.pairscores.chooseStatePairs(this);
			if (!outcome.isEmpty())
			{
				Stack<PairScore> pairsWithScoresComputedUsingGeneralMerger = outcome;
				/*
				new Stack<PairScore>();
				int count=0;
				for(PairScore p:outcome)
				{
					long inconsistencyScore = computeScoreBasedOnInconsistencies(p);
					if (inconsistencyScore >= 0)
					{
						pairsWithScoresComputedUsingGeneralMerger.push(new PairScore(p.getQ(),p.getR(),inconsistencyScore,p.getAnotherScore()));
						if (++count > 10)
							break;
					}
				}

				Collections.sort(pairsWithScoresComputedUsingGeneralMerger);
				*/
				PairScore chosenPair = null;
				if (useClassifyPairs)
				{// This part is to prioritise pairs based on the classify Pairs method.
					Stack<PairScore> NEwresult = MarkovScoreComputation.possibleAtTop(pairsWithScoresComputedUsingGeneralMerger);
					List<PairScore> filter = this.classifyPairs(NEwresult, graph, extendedGraph);

					if(filter.size() >= 1)
						chosenPair = pickPairQSMLike(filter);
					else
						chosenPair = pickPairQSMLike(pairsWithScoresComputedUsingGeneralMerger);
				}
				else
					chosenPair = pickPairQSMLike(pairsWithScoresComputedUsingGeneralMerger);

				outcome.clear();outcome.push(chosenPair);
			}
			
			return outcome;
		}		
		
		/** This method orders the supplied pairs in the order of best to merge to worst to merge. 
		 * We do not simply return the best pair because the next step is to check whether pairs we think are right are classified correctly.
		 * <p/> 
		 * Pairs are supposed to be the ones from {@link LearnerThatCanClassifyPairs#filterPairsBasedOnMandatoryMerge(Stack, LearnerGraph)} where all those not matching mandatory merge conditions are not included.
		 * Inclusion of such pairs will not affect the result but it would be pointless to consider such pairs.
		 * @param extension_graph 
		 * @param learnerGraph 
		 * @param pairs 
		 */
		public List<PairScore> classifyPairs(Collection<PairScore> pairs, LearnerGraph graph, LearnerGraph extension_graph)
		{
			boolean allPairsNegative = true;
			for(PairScore p:pairs)
			{
				assert p.getScore() >= 0;
				
				if (p.getQ().isAccept() || p.getR().isAccept()) // if any are rejects, add with a score of zero, these will always work because accept-reject pairs will not get here and all rejects can be merged.
				{
					allPairsNegative = false;break;
				}
			}
			ArrayList<PairScore> possibleResults = new ArrayList<PairScore>(pairs.size()),nonNegPairs = new ArrayList<PairScore>(pairs.size());
			if (allPairsNegative)
				possibleResults.addAll(pairs);
			else
			{
				for(PairScore p:pairs)
				{
					assert p.getScore() >= 0;
					if (!p.getQ().isAccept() || !p.getR().isAccept()) // if any are rejects, add with a score of zero, these will always work because accept-reject pairs will not get here and all rejects can be merged.
						possibleResults.add(new MarkovPassivePairSelection.PairScoreWithDistance(p,0));
					else
						nonNegPairs.add(p);// meaningful pairs, will check with the classifier
				}
				
				for(PairScore p:nonNegPairs)
				{
					double d = MarkovScoreComputation.computeMMScoreImproved(p,graph, extension_graph);
					if(d >= 0.0)
						possibleResults.add(new MarkovPassivePairSelection.PairScoreWithDistance(p, d));
				}
			
					
				Collections.sort(possibleResults, new Comparator<PairScore>(){
	
					@Override
					public int compare(PairScore o1, PairScore o2) {
						int outcome = sgn( ((MarkovPassivePairSelection.PairScoreWithDistance)o2).getDistanceScore() - ((MarkovPassivePairSelection.PairScoreWithDistance)o1).getDistanceScore());  
						if (outcome != 0)
							return outcome;
						return o2.compareTo(o1);
					}}); 
			}				
			return possibleResults;
		}

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
	
	public static final int []traceQuantityValues = new int[]{2,4,8,16};

//	public static final int []traceQuantityValues = new int[]{2,4,6,8,10,12,14,16};
	public static final double []tracelength = new double[]{0.3,0.5,1.0};

//	public static final int []traceQuantityValues = new int[]{10};
//	public static final double []tracelength = new double[]{1.0};

	public static void runExperiment(String args[]) throws Exception
	{
		Configuration config = Configuration.getDefaultConfiguration().copy();config.setAskQuestions(false);config.setDebugMode(false);config.setGdLowToHighRatio(0.7);config.setRandomPathAttemptFudgeThreshold(1000);
		config.setGdFailOnDuplicateNames(false);
		config.setTransitionMatrixImplType(STATETREE.STATETREE_ARRAY);config.setLearnerScoreMode(ScoreMode.GENERAL);
		ConvertALabel converter = new Transform.InternStringLabel();
		GlobalConfiguration.getConfiguration().setProperty(G_PROPERTIES.LINEARWARNINGS, "false");
//		final int chunkSize = 3;
	
		// Inference from a few traces
		RunSubExperiment<ThreadResult> experimentRunner = new RunSubExperiment<PairQualityLearner.ThreadResult>(ExperimentRunner.getCpuNumber(),"data",args);

		final boolean onlyPositives=true;
		
	

		for(final int preset: new int[]{0})//0,1,2})		
			for(final int traceQuantity:traceQuantityValues)
			for(final double tracelen:tracelength)
			{
				final int traceQuantityToUse = traceQuantity;
			    final AtomicLong comparisonsPerformed = new AtomicLong(0);
			    String selection = "preset="+preset+";quantity="+traceQuantity+";tracelen="+tracelen;

			    //EDSM-Markov Two
			    final RBoxPlotCvs<Double> EDSMMarkovKtwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsEDSMMarkovTwoBCR_"+selection+".csv"));
			    final RBoxPlotCvs<Double> EDSMMarkovKtwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsEDSMMarkovTwoDiff_"+selection+".csv"));

			    //EDSM-Markov three
			    final RBoxPlotCvs<Double> EDSMMarkovKthreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsEDSMMarkovThreeBCR_"+selection+".csv"));
			    final RBoxPlotCvs<Double> EDSMMarkovKthreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsEDSMMarkovThreeDiff_"+selection+".csv"));

			    // EDSM-Markov Four
			    final RBoxPlotCvs<Double> EDSMMarkovKfourBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsEDSMMarkovFourBCR_"+selection+".csv"));
			    final RBoxPlotCvs<Double> EDSMMarkovKfourDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsEDSMMarkovFourDiff_"+selection+".csv"));

			    
			    // SiccoN
			    final RBoxPlotCvs<Double> SiccoNBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsSiccoNBCR_"+selection+".csv"));
			    final RBoxPlotCvs<Double> SiccoNDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsSiccoNDiff_"+selection+".csv"));

				final RWilcoxon <String>  WilcoxonMarkovTwoVsSiccoNBCR=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File("StatisticalTest_"+selection +"_Wilcoxon_t_MarkovTwoVsSiccoNBCR.csv"));
				final RWilcoxon <String>  WilcoxonMarkovThreeVsSiccoNBCR=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File("StatisticalTest_"+selection +"_Wilcoxon_t_MarkovThreeVsSiccoNBCR.csv"));
				final RWilcoxon <String>  WilcoxonMarkovFourVsSiccoNBCR=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File("StatisticalTest_"+selection +"_Wilcoxon_t_MarkovFourVsSiccoNBCR.csv"));

				final RWilcoxon <String>  WilcoxonMarkovTwoVsSiccoNDiff=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File("StatisticalTest_"+selection +"_Wilcoxon_t_MarkovTwoVsSiccoNDiff.csv"));
				final RWilcoxon <String>  WilcoxonMarkovThreeVsSiccoNDiff=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File("StatisticalTest_"+selection +"_Wilcoxon_t_MarkovThreeVsSiccoNDiff.csv"));
				final RWilcoxon <String>  WilcoxonMarkovFourVsSiccoNDiff=new RWilcoxon <String>("BCR, Sicco","BCR, EDSM-Markov learner",new File("StatisticalTest_"+selection +"_Wilcoxon_t_MarkovFourVsSiccoNDiff.csv"));
			
			    final RBoxPlotCvs<Double> gr_TransitionCoverageForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionstransitionCover_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovTwoPrecisionForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovPrecision2_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovTwoRecallForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovRecall2_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovThreePrecisionForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovPrecision3_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovThreeRecallForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovRecall3_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovFourPrecisionForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovPrecision4_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovFourRecallForDifferentLengthOfTraces = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsMarkovRecall4_"+selection+".csv"));
			    
			    final RBoxPlotCvs<Double> MarkovInconsisteciestwo = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsInconsisitecies2_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovInconsisteciesthree = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsInconsisitecies3_"+selection+".csv"));
			    final RBoxPlotCvs<Double> MarkovInconsisteciesfour = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvsNumberOfQuestionsInconsisitecies4_"+selection+".csv"));

				int numberOfTasks = 0;
				numberOfTasks++;
				LearnerRunner learnerRunner = new LearnerRunner(numberOfTasks, config, converter);
				learnerRunner.setOnlyUsePositives(onlyPositives);
//				learnerRunner.setChunkLen(chunkSize);
				learnerRunner.setSelectionID(selection);
				learnerRunner.setPresetLearningParameters(preset);
				learnerRunner.setDisableInconsistenciesInMergers(false);
				learnerRunner.setTraceLengthMultiplier(tracelen);
				learnerRunner.setTraceQuantity(traceQuantity);
				experimentRunner.submitTask(learnerRunner);

				experimentRunner.collectOutcomeOfExperiments(new processSubExperimentResult<PairQualityLearner.ThreadResult>() {

				@Override
				public void processSubResult(ThreadResult result, RunSubExperiment<ThreadResult> experimentrunner) throws IOException 
				{// in these experiments, samples are singleton sequences because we run each of them in a separate process, in order to increase the efficiency with which all tasks are split between CPUs in an iceberg grid.
				
					for(SampleData sample:result.samples)
					{
				
						experimentrunner.Record(EDSMMarkovKthreeBCR,Double.valueOf(sample.EDSMMarkovKthree.numerofstates),sample.EDSMMarkovKthree.differenceBCR.getValue(),"blue",null);
						experimentrunner.Record(EDSMMarkovKthreeDiff,Double.valueOf(sample.EDSMMarkovKthree.numerofstates),sample.EDSMMarkovKthree.differenceStructural.getValue(),"blue",null);

						experimentrunner.Record(EDSMMarkovKtwoBCR,Double.valueOf(sample.EDSMMarkovKtwo.numerofstates),sample.EDSMMarkovKtwo.differenceBCR.getValue(),"blue",null);
						experimentrunner.Record(EDSMMarkovKtwoDiff,Double.valueOf(sample.EDSMMarkovKtwo.numerofstates),sample.EDSMMarkovKtwo.differenceStructural.getValue(),"blue",null);
						
						experimentrunner.Record(EDSMMarkovKfourBCR,Double.valueOf(sample.EDSMMarkovKfour.numerofstates),sample.EDSMMarkovKfour.differenceBCR.getValue(),"blue",null);
						experimentrunner.Record(EDSMMarkovKfourDiff,Double.valueOf(sample.EDSMMarkovKfour.numerofstates),sample.EDSMMarkovKfour.differenceStructural.getValue(),"blue",null);
						
						experimentrunner.Record(SiccoNBCR,Double.valueOf(sample.referenceLearner.numerofstates),sample.referenceLearner.differenceBCR.getValue(),"blue",null);
						experimentrunner.Record(SiccoNDiff,Double.valueOf(sample.referenceLearner.numerofstates),sample.referenceLearner.differenceStructural.getValue(),"blue",null);
					
						experimentrunner.Record(gr_TransitionCoverageForDifferentLengthOfTraces,Double.valueOf(sample.referenceLearner.numerofstates),(double)sample.transitionsSampled,null,null);

						experimentrunner.Record(MarkovTwoPrecisionForDifferentLengthOfTraces,Double.valueOf(sample.EDSMMarkovKtwo.numerofstates),(double)sample.EDSMMarkovKtwo.markovPrecision,null,null);
						experimentrunner.Record(MarkovTwoRecallForDifferentLengthOfTraces,Double.valueOf(sample.EDSMMarkovKtwo.numerofstates),(double)sample.EDSMMarkovKtwo.markovRecall,null,null);
						
						experimentrunner.Record(MarkovThreePrecisionForDifferentLengthOfTraces,Double.valueOf(sample.EDSMMarkovKthree.numerofstates),(double)sample.EDSMMarkovKthree.markovPrecision,null,null);
						experimentrunner.Record(MarkovThreeRecallForDifferentLengthOfTraces,Double.valueOf(sample.EDSMMarkovKthree.numerofstates),(double)sample.EDSMMarkovKthree.markovRecall,null,null);
						
						experimentrunner.Record(MarkovFourPrecisionForDifferentLengthOfTraces,Double.valueOf(sample.EDSMMarkovKfour.numerofstates),(double)sample.EDSMMarkovKfour.markovPrecision,null,null);
						experimentrunner.Record(MarkovFourRecallForDifferentLengthOfTraces,Double.valueOf(sample.EDSMMarkovKfour.numerofstates),(double)sample.EDSMMarkovKfour.markovRecall,null,null);
						
						experimentrunner.Record(MarkovInconsisteciestwo,Double.valueOf(sample.EDSMMarkovKtwo.numerofstates),(double)sample.EDSMMarkovKtwo.inconsistency,null,null);
						experimentrunner.Record(MarkovInconsisteciesthree,Double.valueOf(sample.EDSMMarkovKthree.numerofstates),(double)sample.EDSMMarkovKthree.inconsistency,null,null);
						experimentrunner.Record(MarkovInconsisteciesfour,Double.valueOf(sample.EDSMMarkovKfour.numerofstates),(double)sample.EDSMMarkovKfour.inconsistency,null,null);

						
						experimentrunner.Record(WilcoxonMarkovTwoVsSiccoNBCR,  sample.EDSMMarkovKtwo.differenceBCR.getValue(), sample.referenceLearner.differenceBCR.getValue(), null, null);
						experimentrunner.Record(WilcoxonMarkovThreeVsSiccoNBCR,  sample.EDSMMarkovKthree.differenceBCR.getValue(), sample.referenceLearner.differenceBCR.getValue(), null, null);
						experimentrunner.Record(WilcoxonMarkovFourVsSiccoNBCR,  sample.EDSMMarkovKfour.differenceBCR.getValue(), sample.referenceLearner.differenceBCR.getValue(), null, null);

						experimentrunner.Record(WilcoxonMarkovTwoVsSiccoNDiff,  sample.EDSMMarkovKtwo.differenceStructural.getValue(), sample.referenceLearner.differenceStructural.getValue(), null, null);
						experimentrunner.Record(WilcoxonMarkovThreeVsSiccoNDiff,  sample.EDSMMarkovKthree.differenceStructural.getValue(), sample.referenceLearner.differenceStructural.getValue(), null, null);
						experimentrunner.Record(WilcoxonMarkovFourVsSiccoNDiff,  sample.EDSMMarkovKfour.differenceStructural.getValue(), sample.referenceLearner.differenceStructural.getValue(), null, null);
						
						comparisonsPerformed.addAndGet(sample.comparisonsPerformed);
					}
				}

				@Override
				public String getSubExperimentName()
				{
					return "running tasks for learning whole graphs, preset "+preset;
				}
					
				@SuppressWarnings("rawtypes")
				@Override
				public RGraph[] getGraphs() {
					return new RGraph[]{WilcoxonMarkovTwoVsSiccoNBCR,WilcoxonMarkovTwoVsSiccoNDiff,WilcoxonMarkovThreeVsSiccoNBCR,WilcoxonMarkovThreeVsSiccoNDiff,WilcoxonMarkovFourVsSiccoNBCR,WilcoxonMarkovFourVsSiccoNDiff,MarkovInconsisteciestwo,MarkovInconsisteciesthree,MarkovInconsisteciesfour,MarkovFourPrecisionForDifferentLengthOfTraces,MarkovFourRecallForDifferentLengthOfTraces,MarkovThreePrecisionForDifferentLengthOfTraces,MarkovThreeRecallForDifferentLengthOfTraces,MarkovTwoPrecisionForDifferentLengthOfTraces,MarkovTwoRecallForDifferentLengthOfTraces,EDSMMarkovKthreeBCR,EDSMMarkovKthreeDiff,EDSMMarkovKtwoBCR,EDSMMarkovKtwoDiff,EDSMMarkovKfourBCR,EDSMMarkovKfourDiff,SiccoNBCR,SiccoNDiff,gr_TransitionCoverageForDifferentLengthOfTraces};
				}
					
			});				
			if (experimentRunner.isInteractive())
				System.out.println("\nLOG of comparisons performed: "+Math.log10(comparisonsPerformed.doubleValue())+"\n");
		}
	}
}