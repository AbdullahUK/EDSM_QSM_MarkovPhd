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
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Stack;
import java.util.TreeMap;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import statechum.Configuration;
import statechum.Configuration.STATETREE;
import statechum.Configuration.ScoreMode;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.DeterministicDirectedSparseGraph.VertID;
import statechum.GlobalConfiguration;
import statechum.GlobalConfiguration.G_PROPERTIES;
import statechum.JUConstants;
import statechum.Label;
import statechum.ProgressIndicator;
import statechum.analysis.learning.DrawGraphs;
import statechum.analysis.learning.DrawGraphs.RBoxPlot;
import statechum.analysis.learning.DrawGraphs.RBoxPlotCvs;
import statechum.analysis.learning.DrawGraphs.ScatterPlot;
import statechum.analysis.learning.MarkovClassifier;
import statechum.analysis.learning.MarkovClassifier.ConsistencyChecker;
import statechum.analysis.learning.MarkovModel;
import statechum.analysis.learning.PairScore;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.experiments.ExperimentRunner;
import statechum.analysis.learning.experiments.PaperUAS;
import statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.LearnerThatUsesWekaResults.TrueFalseCounter;
import statechum.analysis.learning.experiments.mutation.DiffExperiments.MachineGenerator;
import statechum.analysis.learning.observers.ProgressDecorator.LearnerEvaluationConfiguration;
import statechum.analysis.learning.rpnicore.LearnerGraph;
import statechum.analysis.learning.rpnicore.MergeStates;
import statechum.analysis.learning.rpnicore.PairScoreComputation.RedNodeSelectionProcedure;
import statechum.analysis.learning.rpnicore.RandomPathGenerator;
import statechum.analysis.learning.rpnicore.RandomPathGenerator.RandomLengthGenerator;
import statechum.analysis.learning.rpnicore.Transform;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;
import statechum.analysis.learning.rpnicore.WMethod;
import statechum.model.testset.PTASequenceEngine;
import statechum.model.testset.PTASequenceEngine.FilterPredicate;
import statechum.analysis.learning.DrawGraphs.RBagPlot;
import statechum.analysis.learning.DrawGraphs.SquareBagPlot;

// This represent the comparsion between EDSM learners and SiccoN.
public class EDSM extends PairQualityLearner
{
	static int i=0;

	public static class LearnerAbortedException extends RuntimeException
	{

		/**
		 * ID for serialisation
		 */
		private static final long serialVersionUID = 5271079210565150062L;
		
		public static void throwExceptionIfTooManyReds( LearnerGraph graph )
		{
			long countOfRed = 0;
			for(CmpVertex v:graph.transitionMatrix.keySet())
				if (v.getColour() == JUConstants.RED)
					if (countOfRed++ > 300)
						throw new LearnerAbortedException();
		}
	}
	
	public static class LearnerRunner implements Callable<ThreadResult>
	{
		protected final Configuration config;
		protected final ConvertALabel converter;
		protected final int states,sample;
		protected boolean onlyUsePositives;
		protected final int seed;
		protected int chunkLen=2;
		protected final int traceQuantity;
		protected String selectionID;
		protected double alphabetMultiplier = 2.;
		protected double traceLengthMultiplier = 2;
		protected double tracesAlphabetMultiplier = 0;
		protected PrintWriter output =null;

		
		public void setout(PrintWriter out) {
			output=out;			
		}
		
		public void setTracesAlphabetMultiplier(double evalAlphabetMult)
		{
			tracesAlphabetMultiplier = evalAlphabetMult;
		}
		
		public void setSelectionID(String value)
		{
			selectionID = value;
		}
		
		public void setTraceLengthMultiplier(double value)
		{
			traceLengthMultiplier = value;
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
		
		public void setChunkLen(int len)
		{
			chunkLen = len;
		}
		
		public LearnerRunner(int argStates, int argSample, int argSeed, int nrOfTraces, Configuration conf, ConvertALabel conv)
		{
			states = argStates;sample = argSample;config = conf;seed = argSeed;traceQuantity=nrOfTraces;converter=conv;
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
			referenceGraph = mg.nextMachine(alphabet,seed, config, converter).pathroutines.buildDeterministicGraph();// reference graph has no reject-states, because we assume that undefined transitions lead to reject states.
			
			LearnerEvaluationConfiguration learnerEval = new LearnerEvaluationConfiguration(config);learnerEval.setLabelConverter(converter);
			final Collection<List<Label>> testSet = PaperUAS.computeEvaluationSet(referenceGraph,states*3,makeEven(2*states*tracesAlphabet));

			for(int attempt=0;attempt<3;++attempt)
			{// try learning the same machine a few times
				LearnerGraph pta = new LearnerGraph(config);
				RandomPathGenerator generator = new RandomPathGenerator(referenceGraph,new Random(attempt),5,null);
				

				int tracesToGenerate = makeEven(traceQuantity);
				if (onlyUsePositives)
					tracesToGenerate = makeEven(traceQuantity)*2;
				final Random rnd = new Random(seed*31+attempt);
				final int pathLength = generator.getPathLength();
				generator.generateRandomPosNeg(tracesToGenerate, 1, false, new RandomLengthGenerator() {
										
						@Override
						public int getLength() {
							return (int) ((rnd.nextInt(pathLength)+1));
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
		
			/*	List<List<Label>> sPlus = generator.getAllSequences(0).getData(new FilterPredicate() {
					@Override
					public boolean shouldBeReturned(Object name) {
						return ((statechum.analysis.learning.rpnicore.RandomPathGenerator.StateName)name).accept;
					}
				});
				List<List<Label>> sMinus= generator.getAllSequences(0).getData(new FilterPredicate() {
					@Override
					public boolean shouldBeReturned(Object name) {
						return !((statechum.analysis.learning.rpnicore.RandomPathGenerator.StateName)name).accept;
					}
				});*/
			/*	assert sPlus.size() > 0;
				assert sMinus.size() > 0;*/
				final MarkovModel m= new MarkovModel(chunkLen,true,true, false);
				new MarkovClassifier(m, pta).updateMarkov(false);
				pta.clearColours();

				if (!onlyUsePositives)
					assert pta.getStateNumber() > pta.getAcceptStateNumber() : "graph with only accept states but onlyUsePositives is not set";
				else 
					assert pta.getStateNumber() == pta.getAcceptStateNumber() : "graph with negatives but onlyUsePositives is set";
				
				LearnerMarkovPassive learnerOfPairs = null;
				LearnerGraph actualAutomaton = null;
				
				final Configuration deepCopy = pta.config.copy();deepCopy.setLearnerCloneGraph(true);
				LearnerGraph ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);

				LearnerGraph trimmedReference = MarkovPassivePairSelection.trimUncoveredTransitions(pta,referenceGraph);
				
				final ConsistencyChecker checker = new MarkovClassifier.DifferentPredictionsInconsistencyNoBlacklisting();
				long inconsistencyForTheReferenceGraph = MarkovClassifier.computeInconsistency(referenceGraph, m, checker, false);
				
				learnerOfPairs = new LearnerMarkovPassive(learnerEval,referenceGraph,pta);learnerOfPairs.setMarkovModel(m);

				learnerOfPairs.setScoreComputationOverride(new RedPriorityOverBluePairSelectionRoutine(m));
				actualAutomaton = learnerOfPairs.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
				
				SampleData dataSample = new SampleData(null,null);
				//dataSample.difference = new DifferenceToReferenceDiff(0, 0);
				//dataSample.differenceForReferenceLearner = new DifferenceToReferenceDiff(0, 0);
				
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
				dataSample.actualLearner = estimateDifference(referenceGraph,actualAutomaton,testSet);
				dataSample.actualLearner.inconsistency = MarkovClassifier.computeInconsistency(actualAutomaton, m, checker, false);
				dataSample.referenceLearner = zeroScore;
				LearnerGraph outcomeOfReferenceLearner = new LearnerGraph(config);
				try
				{
					outcomeOfReferenceLearner = //new ReferenceLearnerUsingSiccoScoring(learnerEval,ptaCopy,false).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
							new EDSMReferenceLearner(learnerEval,ptaCopy,2).learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
					dataSample.referenceLearner = estimateDifference(referenceGraph, outcomeOfReferenceLearner,testSet);
					dataSample.referenceLearner.inconsistency = MarkovClassifier.computeInconsistency(outcomeOfReferenceLearner, m, checker, false);
				}
				catch(LearnerAbortedException ex)
				{// the exception is thrown because the learner failed to learn anything completely. Ignore it because the default score is zero assigned via zeroScore. 
				}				
				dataSample.fractionOfStatesIdentifiedBySingletons=Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph));
				dataSample.stateNumber = referenceGraph.getStateNumber();
				dataSample.transitionsSampled = Math.round(100*trimmedReference.pathroutines.countEdges()/referenceGraph.pathroutines.countEdges());
				statechum.Pair<Double,Double> correctnessOfMarkov = new MarkovClassifier(m, referenceGraph).evaluateCorrectnessOfMarkov();
				dataSample.markovPrecision = Math.round(100*correctnessOfMarkov.firstElem);dataSample.markovRecall = Math.round(100*correctnessOfMarkov.secondElem);
				Collection<List<Label>> wset=WMethod.computeWSet_reducedw(referenceGraph);
				int wSeqLen=0;
				for(List<Label> seq:wset)
				{
					int len = seq.size();if (len > wSeqLen) wSeqLen=len;
				}
				System.out.println("actual: "+actualAutomaton.getStateNumber()+" from reference learner: "+outcomeOfReferenceLearner.getStateNumber()+ 
						" difference actual is "+dataSample.actualLearner.inconsistency+ " difference ref is "+dataSample.referenceLearner.inconsistency
						+ " inconsistency learnt "+dataSample.actualLearner.inconsistency+" inconsistency reference: "+inconsistencyForTheReferenceGraph
						+" transitions per state: "+(double)referenceGraph.pathroutines.countEdges()/referenceGraph.getStateNumber()+
							" W seq max len "+wSeqLen+
							" Uniquely identifiable by W "+Math.round(100*MarkovClassifier.calculateFractionOfIdentifiedStates(referenceGraph, wset))+" %"
						+ " and by singletons "+Math.round(100*MarkovClassifier.calculateFractionOfStatesIdentifiedBySingletons(referenceGraph))+" %"
						);
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
			return outcome;
		}
	}
	
	public static class RedPriorityOverBluePairSelectionRoutine implements statechum.analysis.learning.rpnicore.PairScoreComputation.RedNodeSelectionProcedure
	{
		protected final MarkovModel m;
		
		public RedPriorityOverBluePairSelectionRoutine(MarkovModel mm)
		{
			m=mm;
		}
		
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
		
		LearnerGraph coregraph = null;
		LearnerGraph extendedGraph = null;
		MarkovClassifier cl=null;
		
		@Override
		public void initComputation(LearnerGraph graph) 
		{
			coregraph = graph;

			cl = new MarkovClassifier(m, coregraph);
//		    extendedGraph = cl.constructMarkovTentative();
		}
		
		@Override
		public long overrideScoreComputation(PairScore p) 
		{

			long pairScore = p.getScore();
			
			if (pairScore >= 0)
				pairScore = MarkovScoreComputation.computenewscore(p, extendedGraph);
			
			return pairScore;
		}

		/** This one returns a set of transitions in all directions. */
		@SuppressWarnings("unused")
		@Override
		public Collection<Entry<Label, CmpVertex>> getSurroundingTransitions(CmpVertex currentRed) 
		{
			return null;
		}

	}
	
	public static class EvaluationOfExisingLearnerRunner implements Callable<ThreadResult>
	{
		protected final Configuration config;
		protected final ConvertALabel converter;
		protected final int states,sample;
		protected boolean onlyUsePositives;
		protected final int seed;
		protected int chunkLen=2;
		protected final int traceQuantity;
		protected String selectionID;
		protected double alphabetMultiplier = 2.;
		protected double traceLengthMultiplier = 2;
		protected PrintWriter output =null;

		public void setout(PrintWriter out) {
			output=out;			
		}
		public void setSelectionID(String value)
		{
			selectionID = value;
		}
		
		public void setTraceLengthMultiplier(double value)
		{
			traceLengthMultiplier = value;
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
		
		public void setChunkLen(int len)
		{
			chunkLen = len;
		}
		
		public EvaluationOfExisingLearnerRunner(int argStates, int argSample, int argSeed, int nrOfTraces, Configuration conf, ConvertALabel conv)
		{
			states = argStates;sample = argSample;config = conf;seed = argSeed;traceQuantity=nrOfTraces;converter=conv;
		}
		
		@Override
		public ThreadResult call() throws Exception 
		{
			final int alphabet = (int)(alphabetMultiplier*states);
			LearnerGraph referenceGraph = null;
			ThreadResult outcome = new ThreadResult();
			MachineGenerator mg = new MachineGenerator(states, 400 , (int)Math.round((double)states/5));mg.setGenerateConnected(true);
			referenceGraph = mg.nextMachine(alphabet,seed, config, converter).pathroutines.buildDeterministicGraph();// reference graph has no reject-states, because we assume that undefined transitions lead to reject states.
			
			LearnerEvaluationConfiguration learnerEval = new LearnerEvaluationConfiguration(config);learnerEval.setLabelConverter(converter);
			final Collection<List<Label>> testSet = PaperUAS.computeEvaluationSet(referenceGraph,states*3,makeEven(states*alphabet));
			testSet.addAll(PaperUAS.computeEvaluationSet(referenceGraph,states/2,makeEven(states*alphabet)));
			testSet.addAll(referenceGraph.wmethod.getFullTestSet(2));
			for(int attempt=0;attempt<3;++attempt)
			{// try learning the same machine a few times
				LearnerGraph pta = new LearnerGraph(config);
				RandomPathGenerator generator = new RandomPathGenerator(referenceGraph,new Random(attempt),5,null);
				int tracesToGenerate =0;
				if(onlyUsePositives)
					tracesToGenerate = makeEven(traceQuantity*2);
				else
				   tracesToGenerate = makeEven(traceQuantity);
				final Random rnd = new Random(seed*31+attempt);
				final int pathLength = generator.getPathLength();
			
				generator.generateRandomPosNeg(tracesToGenerate, 1, false, new RandomLengthGenerator() {
					
					@Override
					public int getLength() {
						return (int) ((rnd.nextInt(pathLength)+1));
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
				
				final MarkovModel m= new MarkovModel(chunkLen,true,true, false);
				new MarkovClassifier(m, pta).updateMarkov(false);
				pta.clearColours();

				if (!onlyUsePositives)
					assert pta.getStateNumber() > pta.getAcceptStateNumber() : "graph with only accept states but onlyUsePositives is not set";
				else 
					assert pta.getStateNumber() == pta.getAcceptStateNumber() : "graph with negatives but onlyUsePositives is set";
				
				final Configuration deepCopy = pta.config.copy();deepCopy.setLearnerCloneGraph(true);
				SampleData dataSample=new SampleData();
				dataSample.miscGraphs = new TreeMap<String,ScoresForGraph>();
				List<LearnerThatCanClassifyPairs> learnerList = new ArrayList<LearnerThatCanClassifyPairs>();
				dataSample.referenceGraph=referenceGraph;
				LearnerGraph ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new ReferenceLearnerUsingSiccoScoring(learnerEval,ptaCopy,true));
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new ReferenceLearnerUsingSiccoScoring(learnerEval,ptaCopy,false));
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				if (onlyUsePositives)
				{
					learnerList.add(new KTailsReferenceLearner(learnerEval,ptaCopy,true,1));
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
					learnerList.add(new KTailsReferenceLearner(learnerEval,ptaCopy,true,2));
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
					learnerList.add(new KTailsReferenceLearner(learnerEval,ptaCopy,true,3));
	
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
					learnerList.add(new KTailsReferenceLearner(learnerEval,ptaCopy,false,1));
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
					learnerList.add(new KTailsReferenceLearner(learnerEval,ptaCopy,false,2));
					ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
					learnerList.add(new KTailsReferenceLearner(learnerEval,ptaCopy,false,3));
				}

				
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new EDSMReferenceLearner(learnerEval,ptaCopy,0));
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new EDSMReferenceLearner(learnerEval,ptaCopy,1));
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new EDSMReferenceLearner(learnerEval,ptaCopy,2));
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new EDSMReferenceLearner(learnerEval,ptaCopy,3));
				ptaCopy = new LearnerGraph(deepCopy);LearnerGraph.copyGraphs(pta, ptaCopy);
				learnerList.add(new EDSMReferenceLearner(learnerEval,ptaCopy,4));
				
				i++;
				output.print(i); // second row first column.
				output.print(",");
				output.print("Target");// second row second column
				output.print(",");
				output.print(referenceGraph.getStateNumber());// second row third column
				output.print(",");
				output.print(1);// second row third column
				output.print(",");
				if(onlyUsePositives)
				{
					output.print("Positive Only");// second row third column
					output.print(",");
				}
				if(!onlyUsePositives)
				{
					output.print("Positive and Negative");// second row third column
					output.print(",");
				}
				output.println(1);// second row third column
				output.print("\n");

				for(LearnerThatCanClassifyPairs learnerToUse:learnerList)
					try
					{
						LearnerGraph ref = learnerToUse.learnMachine(new LinkedList<List<Label>>(),new LinkedList<List<Label>>());
						ScoresForGraph l = estimateDifference(referenceGraph,ref,testSet);
						l.statesnumberlearnert=ref.getStateNumber();
						dataSample.miscGraphs.put(learnerToUse.toString(),l);
						output.print(i); // second row first column.
						output.print(",");
						output.print(learnerToUse.toString());// second row second column
						output.print(",");
						output.print(ref.getStateNumber());// second row third column
						output.print(",");
						output.print(l.differenceBCR.getValue());// second row third column
						output.print(",");
						if(onlyUsePositives)
						{
							output.print("Positive Only");// second row third column
							output.print(",");
						}
						if(!onlyUsePositives)
						{
							output.print("Positive and Negative");// second row third column
							output.print(",");
						}
						output.println(l.differenceStructural.getValue());// second row third column
					}
					catch(LearnerAbortedException ex)
					{// the exception is thrown because the learner failed to learn anything completely.
						dataSample.miscGraphs.put(learnerToUse.toString(),zeroScore);
						output.print(i); // second row first column.
						output.print(",");
						output.print(learnerToUse.toString());// second row second column
						output.print(",");
						output.print(0);// second row third column
						output.print(",");
						output.print(0);// second row third column
						output.print(",");
						if(onlyUsePositives)
						{
							output.print("Positive Only");// second row third column
							output.print(",");
						}
						if(!onlyUsePositives)
						{
							output.print("Positive and Negative");// second row third column
							output.print(",");
						}
						output.println(0);// second row third column
						
					}
				System.out.println(dataSample);
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
			return outcome;
		}

		
	}
		
	public static final ScoresForGraph zeroScore;
	static
	{
		zeroScore = new ScoresForGraph();zeroScore.differenceBCR=new DifferenceToReferenceLanguageBCR(0, 0, 0, 0);zeroScore.differenceStructural=new DifferenceToReferenceDiff(0, 0);
	}
	
	/** Merges states using a routing relying on PTA, that faster and consumes less memory than the general one. */
	public static class ReferenceLearnerUsingSiccoScoring extends LearnerThatCanClassifyPairs
	{

		protected final boolean scoringSiccoRecursive;
		
		public ReferenceLearnerUsingSiccoScoring(LearnerEvaluationConfiguration evalCnf, final LearnerGraph argInitialPTA, boolean scoringSiccoRecursive) 
		{
			super(evalCnf,null, argInitialPTA);this.scoringSiccoRecursive = scoringSiccoRecursive;
		}

		/*@Override 
		public LearnerGraph MergeAndDeterminize(LearnerGraph original, StatePair pair)
		{
			return MergeStates.mergeAndDeterminize(original, pair);
		}*/
		
		@Override 
		public Stack<PairScore> ChooseStatePairs(LearnerGraph graph)
		{
			Stack<PairScore> outcome = graph.pairscores.chooseStatePairs(new PairQualityLearner.DefaultRedNodeSelectionProcedure() {

				/* (non-Javadoc)
				 * @see statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.DefaultRedNodeSelectionProcedure#overrideScoreComputation(statechum.analysis.learning.PairScore)
				 */
				@Override
				public long overrideScoreComputation(PairScore p) 
				{
					LearnerAbortedException.throwExceptionIfTooManyReds(coregraph);
					long score = p.getScore();
					if (score >= 0 && coregraph.pairscores.computeScoreSicco(p,scoringSiccoRecursive) < 0)
						score = -1;
					return score;
				}});
			if (!outcome.isEmpty())
			{
				PairScore chosenPair = pickPairQSMLike(outcome);
				outcome.clear();outcome.push(chosenPair);
			}
			
			return outcome;
		}		
		
		@Override
		public String toString()
		{
			return scoringSiccoRecursive? "SiccoR":"SiccoN";
		}
	}
	
	/** This one is a reference learner. */
	public static class KTailsReferenceLearner extends LearnerThatCanClassifyPairs
	{
		private static LearnerEvaluationConfiguration constructConfiguration(LearnerEvaluationConfiguration evalCnf, boolean allPaths, int k)
		{
			Configuration config = evalCnf.config.copy();config.setLearnerScoreMode(allPaths? Configuration.ScoreMode.KTAILS:Configuration.ScoreMode.KTAILS_ANY);config.setKlimit(k);
			LearnerEvaluationConfiguration copy = new LearnerEvaluationConfiguration(config);
			copy.graph = evalCnf.graph;copy.testSet = evalCnf.testSet;
			copy.setLabelConverter(evalCnf.getLabelConverter());
			copy.ifthenSequences = evalCnf.ifthenSequences;copy.labelDetails=evalCnf.labelDetails;
			return copy;
		}
		
		public KTailsReferenceLearner(LearnerEvaluationConfiguration evalCnf, final LearnerGraph argInitialPTA, boolean allPaths, int k) 
		{
			super(constructConfiguration(evalCnf,allPaths,k),null, argInitialPTA);
		}
		
		@Override 
		public Stack<PairScore> ChooseStatePairs(LearnerGraph graph)
		{
			Stack<PairScore> outcome = graph.pairscores.chooseStatePairs(new PairQualityLearner.DefaultRedNodeSelectionProcedure() {

				/* (non-Javadoc)
				 * @see statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.DefaultRedNodeSelectionProcedure#overrideScoreComputation(statechum.analysis.learning.PairScore)
				 */
				@Override
				public long overrideScoreComputation(PairScore p) 
				{
					LearnerAbortedException.throwExceptionIfTooManyReds(coregraph);
					return super.overrideScoreComputation(p);
				}});
			if (!outcome.isEmpty())
			{
				PairScore chosenPair = pickPairQSMLike(outcome);
				outcome.clear();outcome.push(chosenPair);
			}
			
			return outcome;
		}		

		@Override 
		public LearnerGraph MergeAndDeterminize(LearnerGraph original, StatePair pair)
		{
			return MergeStates.mergeAndDeterminize(original, pair);
		}

		@Override
		public String toString()
		{
			return (config.getLearnerScoreMode() == Configuration.ScoreMode.KTAILS? "k-tails":"k-tails(a)")+""+config.getKlimit();
		}		
	}
	
	/** This one is a reference learner. */
	public static class EDSMReferenceLearner extends LearnerThatCanClassifyPairs
	{
		LearnerGraph referenceGraph=null;

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

		public EDSMReferenceLearner(LearnerEvaluationConfiguration evalCnf, final LearnerGraph argInitialPTA, int threshold) 
		{
			super(constructConfiguration(evalCnf,threshold),null, argInitialPTA);
		}

		@Override 
		public Stack<PairScore> ChooseStatePairs(LearnerGraph graph)
		{

			Stack<PairScore> outcome = graph.pairscores.chooseStatePairs(new PairQualityLearner.DefaultRedNodeSelectionProcedure() {

				/* (non-Javadoc)
				 * @see statechum.analysis.learning.experiments.PairSelection.PairQualityLearner.DefaultRedNodeSelectionProcedure#overrideScoreComputation(statechum.analysis.learning.PairScore)
				 */
				@Override
				public long overrideScoreComputation(PairScore p) 
				{
					LearnerAbortedException.throwExceptionIfTooManyReds(coregraph);
					return super.overrideScoreComputation(p);
				}});
			if (!outcome.isEmpty())
			{
				PairScore chosenPair = pickPairQSMLike(outcome);
				outcome.clear();outcome.push(chosenPair);
			}
			
			return outcome;
		}		

		@Override 
		public LearnerGraph MergeAndDeterminize(LearnerGraph original, StatePair pair)
		{
			return MergeStates.mergeAndDeterminize(original, pair);
		}
		
		@Override
		public String toString()
		{
//			return "EDSM>="+config.getRejectPositivePairsWithScoresLessThan();
			return "EDSM>="+config.getGeneralisationThreshold();

		}

		public void setRefGraph(LearnerGraph ref) {
			referenceGraph=ref;			
		}		
	}

	/** Uses the supplied classifier to rank pairs. */
	public static class LearnerMarkovPassive extends LearnerThatCanClassifyPairs
	{
		protected Map<Long,TrueFalseCounter> pairQuality = null;
		private int num_states;
		private int numtraceQuantity;
		private int num_seed;
		private int lengthMultiplier;
		public MarkovModel Markov;
		RedNodeSelectionProcedure computationOverride = null;
		
		public void setPairQualityCounter(Map<Long,TrueFalseCounter> argCounter)
		{
			pairQuality = argCounter;
		}
		
		List<List<List<Label>>> pairsToMerge = null;
		
		public void setPairsToMerge(List<List<List<Label>>> pairs)
		{
			pairsToMerge = pairs;
		}
		
		public List<List<List<Label>>> getPairsToMerge()
		{
			return pairsToMerge;
		}
		
		public void  setlengthMultiplier(int setlengthMultiplier)
		{
			lengthMultiplier = setlengthMultiplier;
		}
		
		public int  getlengthMultiplier()
		{
			return lengthMultiplier;
		}

		public void set_States(int states) 
		{
			num_states=	states;		
		}
		
		public MarkovModel Markov() 
		{
			return Markov;			
		}
			
		public void setMarkovModel(MarkovModel m) 
		{
			Markov=m;
		}

		public void set_traceQuantity(int traceQuantity) 
		{
			numtraceQuantity=traceQuantity;			
		}
		
		public int get_States() 
		{
			return num_states;		
		}
	
		public int get_traceQuantity() 
		{
			return numtraceQuantity;			
		}
		
		public void set_seed(int i) 
		{
			num_seed=i;
		}
		
		public int get_seed() 
		{
			return num_seed;
		}

		public void setScoreComputationOverride(RedNodeSelectionProcedure c)
		{
			computationOverride = c;
		}
		
		
		/** During the evaluation of the red-blue pairs, where all pairs are predicted to be unmergeable, one of the blue states will be returned as red. */
		protected boolean classifierToChooseWhereNoMergeIsAppropriate = false;
		
		/** Used to select next red state based on the subjective quality of the subsequent set of red-blue pairs, as determined by the classifier. */
		protected boolean useClassifierToChooseNextRed = false;
		
		public void setUseClassifierForRed(boolean classifierForRed)
		{
			useClassifierToChooseNextRed = classifierForRed;
		}
		
		public void setUseClassifierToChooseNextRed(boolean classifierToBlockAllMergers)
		{
			classifierToChooseWhereNoMergeIsAppropriate = classifierToBlockAllMergers;
		}

		public LearnerMarkovPassive(LearnerEvaluationConfiguration evalCnf,final LearnerGraph argReferenceGraph, final LearnerGraph argInitialPTA) 
		{
			super(evalCnf,argReferenceGraph,argInitialPTA);
		}
		
		public static String refToString(Object obj)
		{
			return obj == null?"null":obj.toString();
		}
		
		@Override 
		public Stack<PairScore> ChooseStatePairs(final LearnerGraph graph)
		{
			Stack<PairScore> outcome = graph.pairscores.chooseStatePairs(LearnerMarkovPassive.this.computationOverride);
			
			if (!outcome.isEmpty())
			{
				PairScore result = null;
				
				result=pickPairQSMLike(outcome);
				assert result!=null;
				assert result.getScore()>=0;

				outcome.clear();outcome.push(result);
			}	
			return outcome;

		}

		@Override 
		public LearnerGraph MergeAndDeterminize(LearnerGraph original, StatePair pair)
		{
			return MergeStates.mergeAndDeterminize(original, pair);
		}
	}

	public static void main(String args[]) throws Exception
	{
		try
		{
			runExperiment();
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
		
	@SuppressWarnings("null")
	public static void runExperiment() throws Exception
	{
		DrawGraphs gr = new DrawGraphs();
		Configuration config = Configuration.getDefaultConfiguration().copy();config.setAskQuestions(false);config.setDebugMode(false);config.setGdLowToHighRatio(0.7);config.setRandomPathAttemptFudgeThreshold(1000);
		config.setTransitionMatrixImplType(STATETREE.STATETREE_ARRAY);config.setLearnerScoreMode(ScoreMode.GENERAL);
		ConvertALabel converter = new Transform.InternStringLabel();
		GlobalConfiguration.getConfiguration().setProperty(G_PROPERTIES.LINEARWARNINGS, "false");
		final int ThreadNumber = ExperimentRunner.getCpuNumber();	
		ExecutorService executorService = Executors.newFixedThreadPool(ThreadNumber);
		final int minStateNumber = 5;
		final int samplesPerFSM = 10;
		final int stateNumberIncrement = 5;
		final int rangeOfStateNumbers = 45+stateNumberIncrement;
		
		final double traceLengthMultiplierMax = 2;
		final int chunkSize = 2;
		
		FileWriter fw = new FileWriter("EDSM.csv");
		PrintWriter out = new PrintWriter(fw);
		out.print("GraphNumber");// first row first column
		out.print(",");
		out.print("Threshold");// first row second column
		out.print(",");
		out.print("NumberOfStates");// first row third column
		out.print(",");
		out.print("BCR");// first row third column
		out.print(",");
		out.print("PositiveAndNegative");// first row third column
		out.print(",");
		out.println("Structural");// first row third column
		
		final double alphabetMultiplierMax = 2;
		
		/* A very unfavourable case.
		final double traceLengthMultiplierMax = 5;
		final int chunkSize = 4;
		final double alphabetMultiplierMax = 0.5;
		*/
		final String branch = "CAV2014;";
		// Stores tasks to complete.
		CompletionService<ThreadResult> runner = new ExecutorCompletionService<ThreadResult>(executorService);

		final RBoxPlot<String> gr_BCRForDifferentLearners = new RBoxPlot<String>("","BCR",new File(branch+"BCR_learner.pdf"));
		final RBoxPlot<String> gr_StructuralForDifferentLearners = new RBoxPlot<String>("","structural",new File(branch+"structural_learner.pdf"));
		final RBoxPlotCvs<Double> EDSMzeroBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMzeroBCR"+".csv"));
		final RBoxPlotCvs<Double> EDSMoneBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMoneBCR"+".csv"));
		final RBoxPlotCvs<Double> EDSMtwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMtwoBCR"+".csv"));
		final RBoxPlotCvs<Double> EDSMthreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMthreeBCR"+".csv"));
		final RBoxPlotCvs<Double> EDSMFourBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMFourBCR"+".csv"));
		final RBoxPlotCvs<Double> SiccoNBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoNBCR"+".csv"));
		final RBoxPlotCvs<Double> SiccoRBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoRBCR"+".csv"));
		final RBoxPlotCvs<Double> KtailoneBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailoneBCR"+".csv"));
		final RBoxPlotCvs<Double> KtailtwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailtwoBCR"+".csv"));
		final RBoxPlotCvs<Double> KtailthreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailthreeBCR"+".csv"));
		final RBoxPlotCvs<Double> KtailanyoneBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanyoneBCR"+".csv"));
		final RBoxPlotCvs<Double> KtailanytwoBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanytwoBCR"+".csv"));
		final RBoxPlotCvs<Double> KtailanythreeBCR = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanythreeBCR"+".csv"));

		final RBoxPlotCvs<Double> EDSMzeroDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMzeroDiff"+".csv"));
		final RBoxPlotCvs<Double> EDSMoneDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMoneDiff"+".csv"));
		final RBoxPlotCvs<Double> EDSMtwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMtwoDiff"+".csv"));
		final RBoxPlotCvs<Double> EDSMthreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMthreeDiff"+".csv"));
		final RBoxPlotCvs<Double> EDSMFourDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMFourDiff"+".csv"));
		final RBoxPlotCvs<Double> SiccoNDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoNDiff"+".csv"));
		final RBoxPlotCvs<Double> SiccoRDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoRDiff"+".csv"));
		final RBoxPlotCvs<Double> KtailoneDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailoneDiff"+".csv"));
		final RBoxPlotCvs<Double> KtailtwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailtwoDiff"+".csv"));
		final RBoxPlotCvs<Double> KtailthreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailthreeDiff"+".csv"));
		final RBoxPlotCvs<Double> KtailanyoneDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanyoneDiff"+".csv"));
		final RBoxPlotCvs<Double> KtailanytwoDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanytwoDiff"+".csv"));
		final RBoxPlotCvs<Double> KtailanythreeDiff = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_KtailanythreeDiff"+".csv"));

		final RBoxPlotCvs<Double> EDSMzerostates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMzerostates"+".csv"));
		final RBoxPlotCvs<Double> EDSMonestates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMonestates"+".csv"));
		final RBoxPlotCvs<Double> EDSMtwostates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMtwostates"+".csv"));
		final RBoxPlotCvs<Double> EDSMthreestates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMthreestates"+".csv"));
		final RBoxPlotCvs<Double> EDSMFourstates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_EDSMFourstates"+".csv"));
		final RBoxPlotCvs<Double> SiccoNstates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoNstates"+".csv"));
		final RBoxPlotCvs<Double> SiccoRstates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_SiccoRstates"+".csv"));
		final RBoxPlotCvs<Double> Ktailonestates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_Ktailonestates"+".csv"));
		final RBoxPlotCvs<Double> Ktailtwostates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_Ktailtwostates"+".csv"));
		final RBoxPlotCvs<Double> Ktailthreestates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_Ktailthreestates"+".csv"));
		final RBoxPlotCvs<Double> Ktailanyonestates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_Ktailanyonestates"+".csv"));
		final RBoxPlotCvs<Double> Ktailanytwostates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_Ktailanytwostates"+".csv"));
		final RBoxPlotCvs<Double> Ktailanythreestates = new RBoxPlotCvs<Double>("Number Of States","Number Of Questions",new File("RBoxPlotCvs_Ktailanythreestates"+".csv"));
		
		for(final boolean onlyPositives:new boolean[]{true})
			for(final double alphabetMultiplier:new double[]{alphabetMultiplierMax}) 
			{
						try
						{
							int numberOfTasks = 0;
							for(int states=minStateNumber;states < minStateNumber+rangeOfStateNumbers;states+=stateNumberIncrement)
								for(int sample=0;sample<samplesPerFSM;++sample)
								{
									final int traceQuantity=states*5;// half of those generated will be negative that will be thrown away in most experiments.

									final int totalTaskNumber = states*states;
									System.out.println(states);
									EvaluationOfExisingLearnerRunner learnerRunner = new EvaluationOfExisingLearnerRunner(states,sample,totalTaskNumber+numberOfTasks,traceQuantity, config, converter);
									learnerRunner.setOnlyUsePositives(onlyPositives);
									learnerRunner.setAlphabetMultiplier(alphabetMultiplier);
									learnerRunner.setout(out);
									learnerRunner.setTraceLengthMultiplier(traceLengthMultiplierMax);
									learnerRunner.setChunkLen(chunkSize);
									learnerRunner.setSelectionID(branch+"_states"+states+"_sample"+sample);
									runner.submit(learnerRunner);
									++numberOfTasks;
								}
							ProgressIndicator progress = new ProgressIndicator(new Date()+" evaluating "+numberOfTasks+" tasks for the behaviour of different learners", numberOfTasks);
							for(int count=0;count < numberOfTasks;++count)
							{
								ThreadResult result = runner.take().get();// this will throw an exception if any of the tasks failed.
								for(SampleData sample:result.samples)
									for(Entry<String,ScoresForGraph> score:sample.miscGraphs.entrySet())
										gr_StructuralForDifferentLearners.add(score.getKey(),score.getValue().differenceStructural.getValue());
							
								for(SampleData sample:result.samples)
									for(Entry<String,ScoresForGraph> score:sample.miscGraphs.entrySet())
									{
										System.out.println(sample.referenceGraph.getStateNumber());
										gr_BCRForDifferentLearners.add(score.getKey(),score.getValue().differenceBCR.getValue());
									}
								for(SampleData sample:result.samples)
									for(Entry<String,ScoresForGraph> score:sample.miscGraphs.entrySet())
									if(score.getKey().equals("EDSM>=0"))
									{
										EDSMzeroBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										EDSMzeroDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										EDSMzerostates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("EDSM>=1"))
									{
										EDSMoneBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										EDSMoneDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										EDSMonestates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("EDSM>=2"))
									{
										EDSMtwoBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										EDSMtwoDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										EDSMtwostates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("EDSM>=3"))
									{
										EDSMthreeBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										EDSMthreeDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										EDSMthreestates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("EDSM>=4"))
									{
										EDSMFourBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										EDSMFourDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										EDSMFourstates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("SiccoN"))
									{
										SiccoNBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										SiccoNDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										SiccoNstates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);	
									}
									else if(score.getKey().equals("SiccoR"))
									{
										SiccoRBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										SiccoRDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										SiccoRstates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("k-tails(a)1"))
									{
										KtailanyoneBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										KtailanyoneDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										Ktailanyonestates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);										
									}
									else if(score.getKey().equals("k-tails(a)2"))
									{
										KtailanytwoBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										KtailanytwoDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										Ktailanytwostates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("k-tails(a)3"))
									{
										KtailanythreeBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										KtailanythreeDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										Ktailanythreestates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("k-tails1"))
									{
										KtailoneBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										KtailoneDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										Ktailonestates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("k-tails2"))
									{
										KtailtwoBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										KtailtwoDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										Ktailtwostates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
									else if(score.getKey().equals("k-tails3"))
									{
										KtailthreeBCR.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceBCR.getValue(), "blue", null);
										KtailthreeDiff.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), score.getValue().differenceStructural.getValue(), "blue", null);
										Ktailthreestates.addExcel(Double.valueOf(sample.referenceGraph.getStateNumber()), Double.valueOf(score.getValue().statesnumberlearnert), "blue", null);
									}
								progress.next();
								gr_BCRForDifferentLearners.drawInteractive(gr);gr_StructuralForDifferentLearners.drawInteractive(gr);
							}
							
						}
						catch(Exception ex)
						{
							IllegalArgumentException e = new IllegalArgumentException("failed to compute, the problem is: "+ex);e.initCause(ex);
							if (executorService != null) { executorService.shutdownNow();executorService = null; }
							throw e;
						}
			}
		if (gr_BCRForDifferentLearners != null) gr_BCRForDifferentLearners.drawPdf(gr);if (gr_StructuralForDifferentLearners != null) gr_StructuralForDifferentLearners.drawPdf(gr);
		EDSMzeroBCR.drawPdf(gr);EDSMoneBCR.drawPdf(gr);EDSMtwoBCR.drawPdf(gr);EDSMthreeBCR.drawPdf(gr);EDSMFourBCR.drawPdf(gr);
		EDSMzeroDiff.drawPdf(gr);EDSMoneDiff.drawPdf(gr);EDSMtwoDiff.drawPdf(gr);EDSMthreeDiff.drawPdf(gr);EDSMFourDiff.drawPdf(gr);
		EDSMzerostates.drawPdf(gr);EDSMonestates.drawPdf(gr);EDSMtwostates.drawPdf(gr);EDSMthreestates.drawPdf(gr);EDSMFourstates.drawPdf(gr);
		
		SiccoNBCR.drawPdf(gr);SiccoNDiff.drawPdf(gr);SiccoNstates.drawPdf(gr);
		SiccoRBCR.drawPdf(gr);SiccoRDiff.drawPdf(gr);SiccoRstates.drawPdf(gr);
		KtailoneBCR.drawPdf(gr);KtailoneDiff.drawPdf(gr);Ktailonestates.drawPdf(gr);
		KtailtwoBCR.drawPdf(gr);KtailtwoDiff.drawPdf(gr);Ktailtwostates.drawPdf(gr);
		KtailthreeBCR.drawPdf(gr);KtailthreeDiff.drawPdf(gr);Ktailthreestates.drawPdf(gr);
		
		
		KtailanyoneBCR.drawPdf(gr);KtailanyoneDiff.drawPdf(gr);Ktailanyonestates.drawPdf(gr);
		KtailanytwoBCR.drawPdf(gr);KtailanytwoDiff.drawPdf(gr);Ktailanytwostates.drawPdf(gr);
		KtailanythreeBCR.drawPdf(gr);KtailanythreeDiff.drawPdf(gr);Ktailanythreestates.drawPdf(gr);
		  //Flush the output to the file
		   out.flush();
		       
		   //Close the Print Writer
		   out.close();
		       
		   //Close the File Writer
		   fw.close(); 
		if (executorService != null) { executorService.shutdown();executorService = null; }
	}
}