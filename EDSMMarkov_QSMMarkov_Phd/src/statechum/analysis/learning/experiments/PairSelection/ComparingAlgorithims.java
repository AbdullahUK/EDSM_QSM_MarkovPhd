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
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Random;
import java.util.concurrent.Callable;
import java.util.concurrent.atomic.AtomicLong;

import statechum.Configuration;
import statechum.Pair;
import statechum.Configuration.STATETREE;
import statechum.Configuration.ScoreMode;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.DeterministicDirectedSparseGraph.VertID;
import statechum.GlobalConfiguration;
import statechum.GlobalConfiguration.G_PROPERTIES;
import statechum.Label;
import statechum.analysis.learning.DrawGraphs;
import statechum.analysis.learning.DrawGraphs.RBoxPlotCvs;
import statechum.analysis.learning.DrawGraphs.RGraph;
import statechum.analysis.learning.MarkovClassifier;
import statechum.analysis.learning.MarkovModel;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.experiments.ExperimentRunner;
import statechum.analysis.learning.experiments.PaperUAS;
import statechum.analysis.learning.experiments.SGE_ExperimentRunner.RunSubExperiment;
import statechum.analysis.learning.experiments.SGE_ExperimentRunner.processSubExperimentResult;
import statechum.analysis.learning.experiments.PairSelection.Cav2014.KTailsReferenceLearner;
import statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.ReferenceLearner;
import statechum.analysis.learning.experiments.mutation.DiffExperiments.MachineGenerator;
import statechum.analysis.learning.observers.ProgressDecorator.LearnerEvaluationConfiguration;
import statechum.analysis.learning.rpnicore.LearnerGraph;
import statechum.analysis.learning.rpnicore.RandomPathGenerator;
import statechum.analysis.learning.rpnicore.RandomPathGenerator.RandomLengthGenerator;
import statechum.analysis.learning.rpnicore.Transform;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;
import statechum.analysis.learning.rpnicore.WMethod;
import statechum.model.testset.PTASequenceEngine.FilterPredicate;


public class ComparingAlgorithims extends PairQualityLearner
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
				setlearningParameters(true, true, false, true, false);break;
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
			final int alphabet = (int)(alphabetMultiplier*states);
			final int tracesAlphabet = (int)(tracesAlphabetMultiplier*states);
			
			LearnerGraph referenceGraph = null;
			ThreadResult outcome = new ThreadResult();
			MachineGenerator mg = new MachineGenerator(states, 400 , (int)Math.round((double)states/5));mg.setGenerateConnected(true);
			referenceGraph = mg.nextMachine(alphabet,sample, config, converter).pathroutines.buildDeterministicGraph();// reference graph has no reject-states, because we assume that undefined transitions lead to reject states.
			
			LearnerEvaluationConfiguration learnerEval = new LearnerEvaluationConfiguration(config);learnerEval.setLabelConverter(converter);
			final Collection<List<Label>> testSet = PaperUAS.computeEvaluationSet(referenceGraph,states*3,makeEven(states*tracesAlphabet));
			/*for(List<Label> test:testSet)
			{
				Pair<Integer,String> answer = new Pair<Integer,String>(referenceGraph.paths.tracePathPrefixClosed(test),null);
				System.out.println(answer.firstElem);
				System.out.println(test);
				Visualiser.updateFrame(referenceGraph, null);

//				System.out.println(referenceGraph.paths.tracePathPrefixClosed(test, true));
			}*/
			
			// try learning the same machine using a random generator selector passed as a parameter.
			LearnerGraph pta = new LearnerGraph(config);
			RandomPathGenerator generator = new RandomPathGenerator(referenceGraph,new Random(trainingSample),5,null);
			final int tracesToGenerate = makeEven(traceQuantity);
			generator.generateRandomPosNeg(tracesToGenerate, 1, false, new RandomLengthGenerator() {
									
					@Override
					public int getLength() {
						return (int)(traceLengthMultiplier*states*tracesAlphabet);
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
			
			
			final Configuration deepCopy = pta.config.copy();deepCopy.setLearnerCloneGraph(true);
			LearnerGraph ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);

			SampleData dataSample = new SampleData(null,null);
			dataSample.referenceGraph=referenceGraph;
			dataSample.referenceLearner = zeroScore;
			dataSample.SiccoN = zeroScore;
			dataSample.SiccoR = zeroScore;
			dataSample.EDSMzero = zeroScore;
			dataSample.EDSMone = zeroScore;
			dataSample.EDSMtwo = zeroScore;
			dataSample.EDSMthree = zeroScore;
			dataSample.EDSMFour = zeroScore;
			dataSample.ktailsLearner1 = zeroScore;
			dataSample.ktailsLearner2 = zeroScore;
			dataSample.ktailsLearner3 = zeroScore;
			dataSample.ktailsLearner1any = zeroScore;
			dataSample.ktailsLearner2any = zeroScore;
			dataSample.ktailsLearner3any = zeroScore;

			// This is to ensure that scoring is computed in the usual way rather than with override.
			//SiccoN
		
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.COMPATIBILITY);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
//					outcomeOfReferenceLearner = new Cav2014.ReferenceLearnerUsingSiccoScoring(referenceLearnerEval,ptaCopy,false).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					outcomeOfReferenceLearner = new ReferenceLearner(referenceLearnerEval,referenceGraph,ptaCopy,false).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());

					VertID rejectVertexID = null;
					System.out.println("----------------------------------SiccoN----------------------------------");
					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.SiccoN = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.SiccoN=zeroScore;

				}
			}
			
			// This is to ensure that scoring is computed in the usual way rather than with override.
			//SiccoN
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.COMPATIBILITY);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
//					outcomeOfReferenceLearner = new Cav2014.ReferenceLearnerUsingSiccoScoring(referenceLearnerEval,ptaCopy,true).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					outcomeOfReferenceLearner = new ReferenceLearner(referenceLearnerEval,referenceGraph,ptaCopy,true).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());

					VertID rejectVertexID = null;
					System.out.println("----------------------------------SiccoR----------------------------------");

					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.SiccoR = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.SiccoR=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
					System.out.println("----------------------------------EDSM0----------------------------------");

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfReferenceLearner = new Cav2014.EDSMReferenceLearner(referenceLearnerEval,ptaCopy,0).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.EDSMzero = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.EDSMzero=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfReferenceLearner = new Cav2014.EDSMReferenceLearner(referenceLearnerEval,ptaCopy,1).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					System.out.println("----------------------------------EDSM1----------------------------------");

					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.EDSMone = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.EDSMthree=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfReferenceLearner = new Cav2014.EDSMReferenceLearner(referenceLearnerEval,ptaCopy,2).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					System.out.println("----------------------------------EDSM2----------------------------------");

					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.EDSMtwo = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.EDSMtwo=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfReferenceLearner = new Cav2014.EDSMReferenceLearner(referenceLearnerEval,ptaCopy,3).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					System.out.println("----------------------------------EDSM3----------------------------------");

					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.EDSMthree = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.EDSMthree=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(evaluationConfig);

				try
				{
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfReferenceLearner = new Cav2014.EDSMReferenceLearner(referenceLearnerEval,ptaCopy,4).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					System.out.println("----------------------------------EDSM4----------------------------------");

					for(CmpVertex v:outcomeOfReferenceLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfReferenceLearner.nextID(false);
					dataSample.EDSMFour = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.EDSMFour=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfKTailsLearner = new LearnerGraph(evaluationConfig);
				try
				{
					
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfKTailsLearner = new KTailsReferenceLearner(referenceLearnerEval,ptaCopy,true,1).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					System.out.println("----------------------------------K-tails1----------------------------------");

					for(CmpVertex v:outcomeOfKTailsLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfKTailsLearner.nextID(false);
					dataSample.ktailsLearner1 = estimateDifference(referenceGraph, outcomeOfKTailsLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.ktailsLearner1=zeroScore;
				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfKTailsLearner = new LearnerGraph(evaluationConfig);
				try
				{
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfKTailsLearner = new KTailsReferenceLearner(referenceLearnerEval,ptaCopy,true,2).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					System.out.println("----------------------------------K-tails2----------------------------------");

					for(CmpVertex v:outcomeOfKTailsLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfKTailsLearner.nextID(false);
					dataSample.ktailsLearner2 = estimateDifference(referenceGraph, outcomeOfKTailsLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.ktailsLearner2=zeroScore;

				}
			}
		/*	
			{
				LearnerGraph outcomeOfKTailsLearner = new LearnerGraph(evaluationConfig);
				try
				{
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfKTailsLearner = new KTailsReferenceLearner(referenceLearnerEval,ptaCopy,true,3).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					for(CmpVertex v:outcomeOfKTailsLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfKTailsLearner.nextID(false);
					dataSample.ktailsLearner3 = estimateDifference(referenceGraph, outcomeOfKTailsLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.ktailsLearner3=zeroScore;

				}
			}*/
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfKTailsLearner = new LearnerGraph(evaluationConfig);
				try
				{
					System.out.println("----------------------------------K-tails1any----------------------------------");

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfKTailsLearner = new KTailsReferenceLearner(referenceLearnerEval,ptaCopy,false,1).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					for(CmpVertex v:outcomeOfKTailsLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfKTailsLearner.nextID(false);
					dataSample.ktailsLearner1any = estimateDifference(referenceGraph, outcomeOfKTailsLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.ktailsLearner1any=zeroScore;

				}
			}
			
			{
				Configuration evaluationConfig = config.copy();
				evaluationConfig.setLearnerScoreMode(ScoreMode.GENERAL);
				LearnerGraph outcomeOfKTailsLearner = new LearnerGraph(evaluationConfig);
				try
				{
					System.out.println("----------------------------------K-tails2any----------------------------------");

					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfKTailsLearner = new KTailsReferenceLearner(referenceLearnerEval,ptaCopy,false,2).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					for(CmpVertex v:outcomeOfKTailsLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfKTailsLearner.nextID(false);
					dataSample.ktailsLearner2any = estimateDifference(referenceGraph, outcomeOfKTailsLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{
					// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.ktailsLearner2any=zeroScore;
				}
			}
			
			/*{
				LearnerGraph outcomeOfKTailsLearner = new LearnerGraph(evaluationConfig);
				try
				{
					LearnerEvaluationConfiguration referenceLearnerEval = new LearnerEvaluationConfiguration(learnerEval.graph, learnerEval.testSet, evaluationConfig, learnerEval.ifthenSequences, learnerEval.labelDetails);
					outcomeOfKTailsLearner = new KTailsReferenceLearner(referenceLearnerEval,ptaCopy,false,3).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					VertID rejectVertexID = null;
					for(CmpVertex v:outcomeOfKTailsLearner.transitionMatrix.keySet())
						if (!v.isAccept())
						{
							assert rejectVertexID == null : "multiple reject vertices in learnt automaton, such as "+rejectVertexID+" and "+v;
							rejectVertexID = v;break;
						}
					if (rejectVertexID == null)
						rejectVertexID = outcomeOfKTailsLearner.nextID(false);
					dataSample.ktailsLearner3any = estimateDifference(referenceGraph, outcomeOfKTailsLearner,testSet);
				}
				catch(Cav2014.LearnerAbortedException ex)
				{
					// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
					dataSample.ktailsLearner3any=zeroScore;
				}
			}*/

			
			dataSample.fractionOfStatesIdentifiedBySingletons=Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph));
			dataSample.stateNumber = referenceGraph.getStateNumber();
			statechum.Pair<Double,Double> correctnessOfMarkov = new MarkovClassifier(m, referenceGraph).evaluateCorrectnessOfMarkov();
			dataSample.markovPrecision = Math.round(100*correctnessOfMarkov.firstElem);dataSample.markovRecall = Math.round(100*correctnessOfMarkov.secondElem);
//			dataSample.comparisonsPerformed = learnerOfPairs.comparisonsPerformed;
			Collection<List<Label>> wset=WMethod.computeWSet_reducedw(referenceGraph);
			int wSeqLen=0;
			for(List<Label> seq:wset)
			{
				int len = seq.size();if (len > wSeqLen) wSeqLen=len;
			}
//			System.out.println("actual: "+referenceGraph.getStateNumber()+" from reference learner: "+referenceGraph.getStateNumber()+ 
//					" difference actual is "+dataSample.actualLearner.differenceStructural+ " difference ref is "+dataSample.referenceLearner.differenceStructural
//					+ " inconsistency learnt "+dataSample.actualLearner.inconsistency+" inconsistency reference: "+inconsistencyForTheReferenceGraph
//					+" transitions per state: "+(double)referenceGraph.pathroutines.countEdges()/referenceGraph.getStateNumber()+
//						" W seq max len "+wSeqLen+
//						" Uniquely identifiable by W "+Math.round(100*MarkovClassifier.calculateFractionOfIdentifiedStates(referenceGraph, wset))+" %"
//					+ " and by singletons "+Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph))+" %"
//					);
			outcome.samples.add(dataSample);
			
			
			return outcome;
		}

		// Delegates to a specific estimator
		ScoresForGraph estimateDifference(LearnerGraph reference, LearnerGraph actual,Collection<List<Label>> testSet)
		{
			ScoresForGraph outcome = new ScoresForGraph();
			outcome.differenceStructural=DifferenceToReferenceDiff.estimationOfDifferenceDiffMeasure(reference, actual, config, 1);
			outcome.differenceBCR=DifferenceToReferenceLanguageBCR.estimationOfDifference(reference, actual,testSet);
			System.out.println("------------------------------------");
			System.out.println("BCR= "+outcome.differenceBCR.getValue());
			System.out.println("Diff= "+outcome.differenceStructural.getValue());

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
		Configuration config = Configuration.getDefaultConfiguration().copy();config.setAskQuestions(false);config.setDebugMode(false);config.setGdLowToHighRatio(0.7);config.setRandomPathAttemptFudgeThreshold(1000);
		config.setTransitionMatrixImplType(STATETREE.STATETREE_ARRAY);config.setLearnerScoreMode(ScoreMode.GENERAL);
		ConvertALabel converter = new Transform.InternStringLabel();
		GlobalConfiguration.getConfiguration().setProperty(G_PROPERTIES.LINEARWARNINGS, "false");
		final int minStateNumber = 10;
		final int samplesPerFSM = 15;
		final int stateNumberIncrement = 10;
		final int rangeOfStateNumbers = 20+stateNumberIncrement;
		final int trainingSamplesPerFSM = 5;
//		final int traceQuantity = 6;
		final double traceLengthMultiplierMax = 0.5;
		
		final String branch = "OCT2014;";
		RunSubExperiment<ThreadResult> experimentRunner = new RunSubExperiment<PairQualityLearner.ThreadResult>(ExperimentRunner.getCpuNumber(),"data",args);
		// Inference from a few traces
		final boolean onlyPositives=true;
		final double alphabetMultiplierMax=2.0;


	

		for(final int traceQuantity:new int[]{14})
		for(final int preset: new int[]{0})//0,1,2})
		{
			String selection = "preset="+preset+";quantity="+traceQuantity+";tracelen="+traceLengthMultiplierMax+";statesMax="+(minStateNumber+rangeOfStateNumbers-stateNumberIncrement)+";alphabetMult="+alphabetMultiplierMax+";";			

			final RBoxPlotCvs<Double> EDSMzeroBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMzeroBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMoneBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMoneBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMtwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMtwoBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMthreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMthreeBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMfourBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMFourBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> SiccoNBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoNBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> SiccoRBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoRBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailoneBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailoneBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailtwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailtwoBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailthreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailthreeBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailanyoneBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanyoneBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailanytwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanytwoBCR"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailanythreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanythreeBCR"+selection+".csv"));

			final RBoxPlotCvs<Double> EDSMzeroDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMzeroDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMoneDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMoneDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMtwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMtwoDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMthreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMthreeDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> EDSMfourDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMFourDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> SiccoNDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoNDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> SiccoRDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoRDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailoneDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailoneDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailtwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailtwoDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailthreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailthreeDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailanyoneDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanyoneDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailanytwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanytwoDiff"+selection+".csv"));
			final RBoxPlotCvs<Double> KtailanythreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanythreeDiff"+selection+".csv"));	
			final int traceQuantityToUse = traceQuantity;
			final AtomicLong comparisonsPerformed = new AtomicLong(0);
			for(int states=minStateNumber;states < minStateNumber+rangeOfStateNumbers;states+=stateNumberIncrement)
			{
					for(int sample=0;sample<samplesPerFSM;++sample)
						for(int rndSelector=0;rndSelector<trainingSamplesPerFSM;++rndSelector)
						{
							LearnerRunner learnerRunner = new LearnerRunner(states,sample,rndSelector,experimentRunner.getTaskID(),traceQuantityToUse, config, converter);
							learnerRunner.setOnlyUsePositives(onlyPositives);
							learnerRunner.setAlphabetMultiplier(alphabetMultiplierMax);
							learnerRunner.setTracesAlphabetMultiplier(alphabetMultiplierMax);
							learnerRunner.setTraceLengthMultiplier(traceLengthMultiplierMax);
							learnerRunner.setSelectionID(selection);
							learnerRunner.setPresetLearningParameters(preset);
							learnerRunner.setDisableInconsistenciesInMergers(false);
							experimentRunner.submitTask(learnerRunner);
						}
				experimentRunner.collectOutcomeOfExperiments(new processSubExperimentResult<PairQualityLearner.ThreadResult>() {

					@Override
					public void processSubResult(ThreadResult result, RunSubExperiment<ThreadResult> experimentrunner) throws IOException 
					{// in these experiments, samples are singleton sequences because we run each of them in a separate process, in order to increase the efficiency with which all tasks are split between CPUs in an iceberg grid.					
						for(SampleData sample:result.samples)
						{
							experimentrunner.Record(EDSMzeroBCR,sample.referenceGraph.getStateNumber(), sample.EDSMzero.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(EDSMoneBCR,sample.referenceGraph.getStateNumber(), sample.EDSMone.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(EDSMtwoBCR,sample.referenceGraph.getStateNumber(), sample.EDSMtwo.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(EDSMthreeBCR,sample.referenceGraph.getStateNumber(), sample.EDSMthree.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(EDSMfourBCR,sample.referenceGraph.getStateNumber(), sample.EDSMFour.differenceBCR.getValue(), "blue", null);

							experimentrunner.Record(EDSMzeroDiff,sample.referenceGraph.getStateNumber(), sample.EDSMzero.differenceStructural.getValue(), "blue", null);
							experimentrunner.Record(EDSMoneDiff,sample.referenceGraph.getStateNumber(), sample.EDSMone.differenceStructural.getValue(), "blue", null);
							experimentrunner.Record(EDSMtwoDiff,sample.referenceGraph.getStateNumber(), sample.EDSMtwo.differenceStructural.getValue(), "blue", null);
							experimentrunner.Record(EDSMthreeDiff,sample.referenceGraph.getStateNumber(), sample.EDSMthree.differenceStructural.getValue(), "blue", null);
							experimentrunner.Record(EDSMfourDiff,sample.referenceGraph.getStateNumber(), sample.EDSMFour.differenceStructural.getValue(), "blue", null);

							experimentrunner.Record(SiccoRBCR,sample.referenceGraph.getStateNumber(), sample.SiccoR.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(SiccoRDiff,sample.referenceGraph.getStateNumber(), sample.SiccoR.differenceStructural.getValue(), "blue", null);
							
							experimentrunner.Record(SiccoNBCR,sample.referenceGraph.getStateNumber(), sample.SiccoN.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(SiccoNDiff,sample.referenceGraph.getStateNumber(), sample.SiccoN.differenceStructural.getValue(), "blue", null);
							

							experimentrunner.Record(KtailoneBCR,sample.referenceGraph.getStateNumber(), sample.ktailsLearner1.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(KtailtwoBCR,sample.referenceGraph.getStateNumber(), sample.ktailsLearner2.differenceBCR.getValue(), "blue", null);
//							experimentrunner.Record(KtailthreeBCR,sample.referenceGraph.getStateNumber(), sample.ktailsLearner3.differenceBCR.getValue(), "blue", null);
							
							experimentrunner.Record(KtailoneDiff,sample.referenceGraph.getStateNumber(), sample.ktailsLearner1.differenceStructural.getValue(), "blue", null);
							experimentrunner.Record(KtailtwoDiff,sample.referenceGraph.getStateNumber(), sample.ktailsLearner2.differenceStructural.getValue(), "blue", null);
//							experimentrunner.Record(KtailthreeDiff,sample.referenceGraph.getStateNumber(), sample.ktailsLearner3.differenceStructural.getValue(), "blue", null);
							
							experimentrunner.Record(KtailanyoneBCR,sample.referenceGraph.getStateNumber(), sample.ktailsLearner1any.differenceBCR.getValue(), "blue", null);
							experimentrunner.Record(KtailanytwoBCR,sample.referenceGraph.getStateNumber(), sample.ktailsLearner2any.differenceBCR.getValue(), "blue", null);
//							experimentrunner.Record(KtailanythreeBCR,sample.referenceGraph.getStateNumber(), sample.ktailsLearner3any.differenceBCR.getValue(), "blue", null);
							
							experimentrunner.Record(KtailanyoneDiff,sample.referenceGraph.getStateNumber(), sample.ktailsLearner1any.differenceStructural.getValue(), "blue", null);
							experimentrunner.Record(KtailanytwoDiff,sample.referenceGraph.getStateNumber(), sample.ktailsLearner2any.differenceStructural.getValue(), "blue", null);
//							experimentrunner.Record(KtailanythreeDiff,sample.referenceGraph.getStateNumber(), sample.ktailsLearner3any.differenceStructural.getValue(), "blue", null);
							
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
						
						return new RGraph[]{KtailoneDiff,EDSMzeroBCR,EDSMoneBCR,EDSMtwoBCR,EDSMthreeBCR,EDSMfourBCR,
								KtailanythreeDiff,KtailanytwoDiff,KtailanyoneDiff,KtailanythreeBCR,KtailanytwoBCR,KtailanyoneBCR,KtailthreeDiff,KtailtwoDiff,KtailthreeBCR,KtailtwoBCR,KtailoneBCR,EDSMzeroDiff,EDSMoneDiff,EDSMtwoDiff,EDSMthreeDiff,EDSMfourDiff,SiccoRBCR,SiccoNBCR,SiccoRDiff,SiccoNDiff};
					}
					
				});
				

				if (experimentRunner.isInteractive())
					System.out.println("\nLOG of comparisons performed: "+Math.log10(comparisonsPerformed.doubleValue())+"\n");
			}
		}

	
		return experimentRunner.successfulTermination();
	}
	

}

