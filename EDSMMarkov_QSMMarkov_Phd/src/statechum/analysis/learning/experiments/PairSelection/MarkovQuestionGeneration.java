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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map.Entry;

import statechum.Configuration;
import statechum.GlobalConfiguration;
import statechum.JUConstants;
import statechum.Label;
import statechum.Pair;
import statechum.Configuration.STATETREE;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.JUConstants.PAIRCOMPATIBILITY;
import statechum.Trace;
import statechum.analysis.learning.AbstractOracle;
import statechum.analysis.learning.MarkovModel;
import statechum.analysis.learning.MarkovModel.MarkovOutcome;
import statechum.analysis.learning.PairScore;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.MarkovModel.UpdatablePairInteger;
import statechum.analysis.learning.rpnicore.AMEquivalenceClass;
import statechum.analysis.learning.rpnicore.AbstractLearnerGraph;
import statechum.analysis.learning.rpnicore.LearnerGraph;
import statechum.analysis.learning.rpnicore.LearnerGraphCachedData;
import statechum.collections.ArrayMapWithSearch;
import statechum.collections.HashMapWithSearch;

public class MarkovQuestionGeneration {
/*	public UpdatablePairInteger ask_questions(PairScore Pair, LearnerGraph graph, LearnerGraph extension_Graph2, LearnerGraph referenceGraph)
	{
		long num_queries=0;
		Collection<List<Label>> SmartQuestions = new LinkedList<List<Label>>();
	    SmartQuestions = computeSQS(Pair, graph, extension_Graph2);// questions generator from the current pair
	    SmartQuestions.addAll(computeScoreSiccoQuestions(graph, Pair));
		for(List<Label> question:SmartQuestions)
		{
			if (GlobalConfiguration.getConfiguration().isAssertEnabled())												
				if (graph.paths.tracePathPrefixClosed(question) == AbstractOracle.USER_ACCEPTED)
				{
					throw new IllegalArgumentException("question "+ question+ " has already been answered");
				}				
		}
	    if(SmartQuestions!=null && SmartQuestions.size() > 0) 
	    {
	    	// asking those questions 
			Iterator<List<Label>> questionIt = SmartQuestions.iterator();	
			while(questionIt.hasNext())
			{
    			List<Label> question = questionIt.next();
    			Pair<Integer,String> answer = null;
    			assert question!=null;	
//				System.out.println(question + "  "+p);
    			answer = new Pair<Integer,String>(referenceGraph.paths.tracePathPrefixClosed(question),null);										
				if (answer.firstElem == AbstractOracle.USER_ACCEPTED) 
				{
					synchronized (AbstractLearnerGraph.syncObj) 
					{
						Label label=question.get(question.size()-1);
						CmpVertex state = graph.getVertex(question.subList(0, question.size()-1));
						assert state.isAccept();												
						
						if(!graph.transitionMatrix.get(state).keySet().contains(label) && state.isAccept()==true)
						{
							extendWithLabel(graph,state, true, question.get(question.size()-1));
							num_queries++;
							if (graph.pairscores.computePairCompatibilityScore(Pair) < 0)
							{
								return new UpdatablePairInteger(-1,num_queries);
							}

	
						}
												
																		
					}
				} 
				else if (answer.firstElem >= 0) 
				{
					synchronized (AbstractLearnerGraph.syncObj) 
					{
						Label label=question.get(question.size()-1);
						CmpVertex state = graph.getVertex(question.subList(0, question.size()-1));
						assert state.isAccept();												
						
						if(!graph.transitionMatrix.get(state).keySet().contains(label) && state.isAccept()==true)
						{
							extendWithLabel(graph,state, false,question.get(question.size()-1));
							num_queries++;
							if (graph.pairscores.computePairCompatibilityScore(Pair) < 0)
							{
								return new UpdatablePairInteger(-1,num_queries);

							}								
						}
					}
				}				
				else
					throw new IllegalArgumentException("unexpected user choice "+answer);
				
			}
	    }
	    return new UpdatablePairInteger(0,num_queries);
	}*/
	
	class UpdatablePairInteger
	{
		public long scoreOfComputation, NumberOfQueries;
		public UpdatablePairInteger(long a, long b) {
			scoreOfComputation=a;NumberOfQueries=b;
		}
		
		@Override
		public String toString()
		{
			return "(scoreOfComputation: "+scoreOfComputation+", NumberOfQueries: "+NumberOfQueries+")";
		}
	}
	
	public static Collection<List<Label>> computeSQSImproved(PairScore pair, LearnerGraph graph, LearnerGraph extension_Graph2) 
	{
		if(pair.firstElem.isAccept()!=true && pair.secondElem.isAccept()!=true)
			return new TreeSet<List<Label>>();
		
//		Visualiser.updateFrame(graph, null);

		Set<Label> outgoing_form_blue_node = new HashSet<Label>();
		Set<Label> outgoing_form_red_node = new HashSet<Label>();
		Set<Label> predicted_form_blue_node = new HashSet<Label>();
		Set<Label> predicted_form_red_node = new HashSet<Label>();
		
		
		Set<List<Label>> questionAdded = new HashSet<List<Label>>();
		
		outgoing_form_blue_node = graph.transitionMatrix.get(pair.getQ()).keySet();
		outgoing_form_red_node = graph.transitionMatrix.get(pair.getR()).keySet();
		predicted_form_blue_node = extension_Graph2.transitionMatrix.get(pair.getQ()).keySet();
		predicted_form_red_node = extension_Graph2.transitionMatrix.get(pair.getR()).keySet();
		Map<CmpVertex,List<Label>> existingPathToState = graph.pathroutines.computeShortPathsToAllStates();						

		for(Label out_red:predicted_form_red_node)
		{	
			if(!outgoing_form_blue_node.contains(out_red) && extension_Graph2.transitionMatrix.get(pair.getR()).get(out_red).isAccept()==true)
			{						
				LinkedList<Label> question = new LinkedList<Label>();
				assert question.size() == 0;
				question.addAll(existingPathToState.get(pair.getQ()));question.add(out_red);
				if (graph.paths.tracePathPrefixClosed(question) != AbstractOracle.USER_ACCEPTED)
				{	
					questionAdded.add(question);
				}
			}
		}
		
		for(Label out_blue:predicted_form_blue_node)
		{			
			if(!outgoing_form_red_node.contains(out_blue) && extension_Graph2.transitionMatrix.get(pair.getQ()).get(out_blue).isAccept()==true)
			{			
				LinkedList<Label> question = new LinkedList<Label>();
				assert question.size() == 0;
				question.addAll(existingPathToState.get(pair.getR()));question.add(out_blue);
				if (graph.paths.tracePathPrefixClosed(question) != AbstractOracle.USER_ACCEPTED)
				{	
					questionAdded.add(question);
				}
			}
		}
		
		return questionAdded;
	}
	
	public static Collection<List<Label>> computeSymmetricQueries(PairScore pair, LearnerGraph graph, LearnerGraph extension_Graph2,boolean recursive) 
	{
		if(pair.firstElem.isAccept()!=true && pair.secondElem.isAccept()!=true)
			return new TreeSet<List<Label>>();
		Set<List<Label>> questionAdded = new HashSet<List<Label>>();

		assert pair.getQ() != pair.getR();
		assert graph.transitionMatrix.containsKey(pair.firstElem);
		assert graph.transitionMatrix.containsKey(pair.secondElem);
		Map<CmpVertex,List<CmpVertex>> mergedVertices = graph.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(graph.getStateNumber()):
				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(graph.getStateNumber());
		Configuration shallowCopy = graph.config.copy();shallowCopy.setLearnerCloneGraph(false);
		long pairScore = graph.pairscores.computePairCompatibilityScore_bluefringe(pair,mergedVertices);
		if (pairScore < 0)
			return new HashSet<List<Label>>();
		
//		Collection<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> collectionOfVerticesToMerge = new ArrayList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();
//		pairScore = graph.pairscores.computePairCompatibilityScore_general(pair,null,collectionOfVerticesToMerge);
		
		//This mean one of the red state can make move while the blue state does not in this case asking symmetric
		/*if(mergedVertices.get(pair.getR())==null)
		{
			questionAdded.addAll(computeSQS_old(pair,graph,extension_Graph2));
		}*/
		
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:graph.transitionMatrix.entrySet())
			if ((recursive || entry.getKey() == pair.getR())) //&& entry.getKey().getColour() == JUConstants.RED)
			{// only checks for specific state of interest if we are supposed to be non-recursive.
				CmpVertex mergednode = entry.getKey();
				if (mergedVertices.containsKey(mergednode))
				{	
					for(CmpVertex Tomerge:mergedVertices.get(mergednode))
					{
						PairScore newpair=new PairScore(Tomerge, mergednode, 0, 0);
						questionAdded.addAll(computeOneStep(newpair,graph,extension_Graph2, recursive));
					}
				}
			}
		
		return questionAdded;
	}
	
	/** 
	 * It computes queries based on labels that are exist from the merged (red) nodes and not from the (blue) nodes.
	 * 
	 * @param pair
	 * @param graph is current graph.
	 * @param MarkovGraph is graph with extension based on Markov predictions.
	 * @param verticesToMerge are vertices that would be merged.
	 * @param checkInconsistecy 
	 * @return collection of queries.
	 */
	public static Collection<List<Label>> computeSymmetricQueriesBasedOnGeneralScore(PairScore pair, LearnerGraph graph, LearnerGraph extension_Graph2,boolean recursive, List<AMEquivalenceClass<CmpVertex, LearnerGraphCachedData>> verticesToMerge, boolean checkInconsistecy) 
	{
		if(pair.firstElem.isAccept()!=true && pair.secondElem.isAccept()!=true)
			return new TreeSet<List<Label>>();
		Set<List<Label>> questionAdded = new HashSet<List<Label>>();

		assert pair.getQ() != pair.getR();
		assert graph.transitionMatrix.containsKey(pair.firstElem);
		assert graph.transitionMatrix.containsKey(pair.secondElem);
				
		Set<CmpVertex> affectedVerticesInMergedGraph = new LinkedHashSet<CmpVertex>();
		Map<CmpVertex,ArrayList<CmpVertex>> allstatestomergedwith = new TreeMap<CmpVertex,ArrayList<CmpVertex>>(); 
		for(AMEquivalenceClass<CmpVertex,LearnerGraphCachedData> eqClass:verticesToMerge)
			if(eqClass.getStates().size() > 1 && eqClass.getMergedVertex().isAccept())
			if (recursive || eqClass.getStates().contains(pair.getR()))
			{
				ArrayList<CmpVertex> toMergewith=new ArrayList<CmpVertex>();
				affectedVerticesInMergedGraph.add(eqClass.getMergedVertex());
				for(CmpVertex current:eqClass.getStates())
				{
					if(!current.getStringId().equals(eqClass.getMergedVertex().getStringId()))
						toMergewith.add(current);
				}
				allstatestomergedwith.put(eqClass.getMergedVertex(), toMergewith);
			}
	
		
		for(CmpVertex mergednode:affectedVerticesInMergedGraph)
		{
			for(CmpVertex toMerge:allstatestomergedwith.get(mergednode))
			{			
				assert mergednode.getIntegerID()!=toMerge.getIntegerID();				
				PairScore newpair=new PairScore(toMerge, mergednode, 0, 0);
				questionAdded.addAll(computeOneStep(newpair,graph,extension_Graph2, checkInconsistecy));
			}
		}
		return questionAdded;
	}
	
//	/** 
//	 * It computes a steps queries of a pair of states.
//	 * It can be seen as filling the missing tails of the current pairs by asking those queries
//	 * 
//	 * @param graph is current graph.
//	 * @param pair
//	 * @param number of steps from the pair of states.
//	 * @return a pair of states to be merged or null if the graph is deterministic.
//	 */
//	public static Collection<List<Label>> computeStepsImproved(LearnerGraph graph, PairScore pair, int numberofsteps,boolean recursive) 
//	{
//		if(pair.firstElem.isAccept()!=true && pair.secondElem.isAccept()!=true)
//			return new TreeSet<List<Label>>();
//		Set<List<Label>> questionAdded = new HashSet<List<Label>>();
//
//		assert pair.getQ() != pair.getR();
//		assert graph.transitionMatrix.containsKey(pair.firstElem);
//		assert graph.transitionMatrix.containsKey(pair.secondElem);
//		Map<CmpVertex,List<CmpVertex>> mergedVertices = graph.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
//				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(graph.getStateNumber()):
//				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(graph.getStateNumber());
//		Configuration shallowCopy = graph.config.copy();shallowCopy.setLearnerCloneGraph(false);
//		long pairScore = graph.pairscores.computePairCompatibilityScore_internal(pair,mergedVertices);
//		if (pairScore < 0)
//			return null;
////			throw new IllegalArgumentException("elements of the pair are incompatible");
//		
//		if(mergedVertices.get(pair.getR())==null)
//			questionAdded.addAll(computeStepsQueries(graph,pair, numberofsteps));
//
//		
//		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:graph.transitionMatrix.entrySet())
//			if ((recursive || entry.getKey() == pair.getR())) //&& entry.getKey().getColour() == JUConstants.RED)
//			{// only checks for specific state of interest if we are supposed to be non-recursive.
//				CmpVertex vert = entry.getKey();
//				if (mergedVertices.containsKey(vert))
//				{	
//					for(CmpVertex current:mergedVertices.get(vert))
//					{
//						PairScore newpair=new PairScore(current, vert, 0, 0);
//						questionAdded.addAll(computeStepsQueries(graph,newpair, numberofsteps));
//					}
//				}
//			}
//		
//		return questionAdded;
//	}
	
	public static Collection<List<Label>> computeSQS(PairScore pair, LearnerGraph graph, LearnerGraph extension_Graph2) 
	{
		if(pair.firstElem.isAccept()!=true && pair.secondElem.isAccept()!=true)
			return new TreeSet<List<Label>>();
		
//		Visualiser.updateFrame(graph, null);

		Set<Label> outgoing_form_blue_node = new HashSet<Label>();
		Set<Label> outgoing_form_red_node = new HashSet<Label>();
		Set<Label> predicted_form_blue_node = new HashSet<Label>();
		Set<Label> predicted_form_red_node = new HashSet<Label>();
		
		
		Set<List<Label>> questionAdded = new HashSet<List<Label>>();
		
		outgoing_form_blue_node = graph.transitionMatrix.get(pair.getQ()).keySet();
		outgoing_form_red_node = graph.transitionMatrix.get(pair.getR()).keySet();
		predicted_form_blue_node = extension_Graph2.transitionMatrix.get(pair.getQ()).keySet();
		predicted_form_red_node = extension_Graph2.transitionMatrix.get(pair.getR()).keySet();
		Map<CmpVertex,List<Label>> existingPathToState = graph.pathroutines.computeShortPathsToAllStates();	
		Set<Label> Allpredicted = new HashSet<Label>();
		Allpredicted.addAll(predicted_form_red_node);
		Allpredicted.addAll(predicted_form_blue_node);

		for(Label predicted:Allpredicted)
		{	
			if(!outgoing_form_blue_node.contains(predicted))// && extension_Graph2.transitionMatrix.get(pair.getR()).get(out_red).isAccept()==true)
			{						
				LinkedList<Label> question = new LinkedList<Label>();
				assert question.size() == 0;
				question.addAll(existingPathToState.get(pair.getQ()));
				question.add(predicted);
				if (graph.paths.tracePathPrefixClosed(question) != AbstractOracle.USER_ACCEPTED )
				{	
					questionAdded.add(question);
				}
			}
							
			if(!outgoing_form_red_node.contains(predicted))// && extension_Graph2.transitionMatrix.get(pair.getQ()).get(out_blue).isAccept()==true)
			{			
				LinkedList<Label> question = new LinkedList<Label>();
				assert question.size() == 0;
				question.addAll(existingPathToState.get(pair.getR()));question.add(predicted);
				if (graph.paths.tracePathPrefixClosed(question) != AbstractOracle.USER_ACCEPTED)
				{	
					questionAdded.add(question);
				}
			}
		}
		
		return questionAdded;
	}
	
	public static Collection<List<Label>> computeOneStep(PairScore pair, LearnerGraph graph, LearnerGraph extendedGraph, boolean checkInconsistecy) 
	{
		if(pair.firstElem.isAccept()!=true && pair.secondElem.isAccept()!=true)
			return new TreeSet<List<Label>>();
		
		Set<Label> outgoing_form_blue_node = new HashSet<Label>();
		Set<Label> outgoing_form_red_node = new HashSet<Label>();		
		Set<List<Label>> questionAdded = new HashSet<List<Label>>();
		outgoing_form_blue_node = graph.transitionMatrix.get(pair.getQ()).keySet();
		outgoing_form_red_node = graph.transitionMatrix.get(pair.getR()).keySet();
		Map<CmpVertex,List<Label>> stateCover = graph.pathroutines.computeShortPathsToAllStates();	
				
		if(checkInconsistecy)
		{
			for(Label out_red:outgoing_form_red_node)
			{	
				// this is to ask from the blue states any existing and predicted from the red states that are not in the blue states.
				if(!outgoing_form_blue_node.contains(out_red) && graph.transitionMatrix.get(pair.getR()).get(out_red).isAccept())
				{						
					LinkedList<Label> question = new LinkedList<Label>();
					assert question.size() == 0;
					question.addAll(stateCover.get(pair.getQ()));
					question.add(out_red);
					
					if (graph.paths.getVertex(question)==null && extendedGraph.transitionMatrix.get(pair.getQ()).get(out_red)==null)
					{	
						questionAdded.add(question);
					}
					//conflict in prediction

					else if (graph.paths.getVertex(question)==null &&  extendedGraph.transitionMatrix.get(pair.getQ()).get(out_red).isAccept()!=graph.transitionMatrix.get(pair.getR()).get(out_red).isAccept())
					{
						questionAdded.add(question);
					}
				}
			}
		}
		else
		{
			for(Label out_red:outgoing_form_red_node)
			{	
				// this is to ask from the blue states any existing and predicted from the red states that are not in the blue states.
				if(!outgoing_form_blue_node.contains(out_red) && graph.transitionMatrix.get(pair.getR()).get(out_red).isAccept())
				{						
					LinkedList<Label> question = new LinkedList<Label>();
					assert question.size() == 0;
					question.addAll(stateCover.get(pair.getQ()));
					question.add(out_red);
					if (graph.paths.getVertex(question)==null)
					{	
						questionAdded.add(question);
					}
				}
			}

		}
		return questionAdded;
	}
	
	public static Collection<List<Label>> computestepsQueries(LearnerGraph coregraph, StatePair pair,int numberofsteps)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		if (!AbstractLearnerGraph.checkCompatible(pair.getR(),pair.getQ(),coregraph.pairCompatibility))
			return new ArrayList<List<Label>>();

		int currentExplorationDepth=0;
		assert pair.getQ() != pair.getR();
		boolean foundKTail = false;
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();						

		Queue<StatePair> currentExplorationBoundary = new LinkedList<StatePair>();// FIFO queue
		currentExplorationBoundary.add(pair);currentExplorationBoundary.offer(null);
		
		while(!foundKTail)
		{
			StatePair currentPair = currentExplorationBoundary.remove();
			if (currentPair == null)
			{// we got to the end of a wave
				if (currentExplorationBoundary.isEmpty())
					break;// we are at the end of the last wave, stop looping.

				// mark the end of a wave.
				currentExplorationBoundary.offer(null);currentExplorationDepth++;
			}
			else
			{
				Map<Label,CmpVertex> targetRed = coregraph.transitionMatrix.get(currentPair.getR()),
					targetBlue = coregraph.transitionMatrix.get(currentPair.getQ());
	
				for(Entry<Label,CmpVertex> redEntry:targetRed.entrySet())
				{
					CmpVertex nextBlueState = targetBlue.get(redEntry.getKey());
					if (nextBlueState != null)
					{// both states can make a transition
						if (!AbstractLearnerGraph.checkCompatible(redEntry.getValue(),nextBlueState,coregraph.pairCompatibility))
							return new ArrayList<List<Label>>();// incompatible states						
						if (currentExplorationDepth >= numberofsteps)
						{
							foundKTail = true;
							break;//  the "currentExplorationDepth" length reachs the number of steps want. stop exploration
						}							
						StatePair nextStatePair = new StatePair(nextBlueState,redEntry.getValue());
						currentExplorationBoundary.offer(nextStatePair);
					}
					else
					{
						LinkedList<Label> questiontoblue = new LinkedList<Label>();
						questiontoblue.addAll(stateCover.get(currentPair.getQ()));
						questiontoblue.add(redEntry.getKey());
//						if (coregraph.paths.tracePathPrefixClosed(questiontoblue) != AbstractOracle.USER_ACCEPTED && redEntry.getValue().isAccept())
						//if (coregraph.paths.tracePathPrefixClosed(questiontoblue) != AbstractOracle.USER_ACCEPTED is always true
						if (coregraph.paths.getVertex(questiontoblue) == null)// && redEntry.getValue().isAccept())
						{	
							questionAdded.add(questiontoblue);
						}
					}
				}
			}
		}
		
		
		if (foundKTail)
		{
			return questionAdded;
		}
		return questionAdded;
	}
	
	public static Collection<List<Label>>  computeKtailQueriesimproved(LearnerGraph coregraph, StatePair pair, int numberofsteps)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();

		if (!AbstractLearnerGraph.checkCompatible(pair.getR(),pair.getQ(),coregraph.pairCompatibility))
			return new ArrayList<List<Label>>();

		int currentExplorationDepth=1;// when we look at transitions from the initial pair of states, this is depth 1.
		assert pair.getQ() != pair.getR();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();						

		Queue<StatePair> currentExplorationBoundary = new LinkedList<StatePair>();// FIFO queue
		if (currentExplorationDepth <= numberofsteps)
			currentExplorationBoundary.add(pair);
		currentExplorationBoundary.offer(null);
		
		while(true) // we'll do a break at the end of the last wave
		{
			StatePair currentPair = currentExplorationBoundary.remove();
			if (currentPair == null)
			{// we got to the end of a wave
				if (currentExplorationBoundary.isEmpty())
					break;// we are at the end of the last wave, stop looping.

				// mark the end of a wave.
				currentExplorationBoundary.offer(null);currentExplorationDepth++;
			}
			else
			{
				Map<Label,CmpVertex> targetRed = coregraph.transitionMatrix.get(currentPair.getR()),
					targetBlue = coregraph.transitionMatrix.get(currentPair.getQ());
	
				for(Entry<Label,CmpVertex> redEntry:targetRed.entrySet())
				{
					CmpVertex nextBlueState = targetBlue.get(redEntry.getKey());
					if (nextBlueState != null)
					{// both states can make a transition
						if (!AbstractLearnerGraph.checkCompatible(redEntry.getValue(),nextBlueState,coregraph.pairCompatibility))
							return new ArrayList<List<Label>>();// definitely incompatible states, fail regardless whether we should look for a single or all paths. 
												
						if (currentExplorationDepth < numberofsteps)
						{// if our current depth is less than the one to explore, make subsequent steps.
							StatePair nextStatePair = new StatePair(nextBlueState,redEntry.getValue());
							currentExplorationBoundary.offer(nextStatePair);
						}
						// If we did not take the above condition (aka reached the maximal depth to explore), we still cannot break out of a loop even if we have anyPath
						// set to true, because there could be transitions leading to states with different accept-conditions, hence explore all matched transitions.						
					}
					else
					{
						LinkedList<Label> questiontoblue = new LinkedList<Label>();
						questiontoblue.addAll(stateCover.get(currentPair.getQ()));
						questiontoblue.add(redEntry.getKey());
//						if (coregraph.paths.tracePathPrefixClosed(questiontoblue) != AbstractOracle.USER_ACCEPTED && redEntry.getValue().isAccept())
						//if (coregraph.paths.tracePathPrefixClosed(questiontoblue) != AbstractOracle.USER_ACCEPTED is always true
						if (coregraph.paths.getVertex(questiontoblue) == null && redEntry.getValue().isAccept())
						{	
							questionAdded.add(questiontoblue);
						}
					}
				}
				
			}
		}
		
		return questionAdded;// if no transitions matched in a wave, this means that we reached tail-end of a graph before exhausting the exploration depth, thus the score is -1.
	}
	
	
	public static Collection<List<Label>> computeKtailQueries(LearnerGraph coregraph, StatePair pair,int numberofsteps)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		if (!AbstractLearnerGraph.checkCompatible(pair.getR(),pair.getQ(),coregraph.pairCompatibility))
			return new ArrayList<List<Label>>();

		int currentExplorationDepth=0;
		assert pair.getQ() != pair.getR();
		boolean foundKTail = false;
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();						

		Queue<StatePair> currentExplorationBoundary = new LinkedList<StatePair>();// FIFO queue
		currentExplorationBoundary.add(pair);currentExplorationBoundary.offer(null);
		
		while(!foundKTail)
		{
			StatePair currentPair = currentExplorationBoundary.remove();
			if (currentPair == null)
			{// we got to the end of a wave
				if (currentExplorationBoundary.isEmpty())
					break;// we are at the end of the last wave, stop looping.

				// mark the end of a wave.
				currentExplorationBoundary.offer(null);currentExplorationDepth++;
			}
			else
			{
				Map<Label,CmpVertex> targetRed = coregraph.transitionMatrix.get(currentPair.getR()),
					targetBlue = coregraph.transitionMatrix.get(currentPair.getQ());
	
				for(Entry<Label,CmpVertex> redEntry:targetRed.entrySet())
				{
					CmpVertex nextBlueState = targetBlue.get(redEntry.getKey());
					if (nextBlueState != null)
					{// both states can make a transition
						if (!AbstractLearnerGraph.checkCompatible(redEntry.getValue(),nextBlueState,coregraph.pairCompatibility))
							return new ArrayList<List<Label>>();// incompatible states						
						if (currentExplorationDepth >= numberofsteps)
						{
							foundKTail = true;
							break;//  the "currentExplorationDepth" length reachs the number of steps want. stop exploration
						}							
						StatePair nextStatePair = new StatePair(nextBlueState,redEntry.getValue());
						currentExplorationBoundary.offer(nextStatePair);
					}
					else
					{
						LinkedList<Label> questiontoblue = new LinkedList<Label>();
						questiontoblue.addAll(stateCover.get(currentPair.getQ()));
						questiontoblue.add(redEntry.getKey());
//						if (coregraph.paths.tracePathPrefixClosed(questiontoblue) != AbstractOracle.USER_ACCEPTED && redEntry.getValue().isAccept())
						//if (coregraph.paths.tracePathPrefixClosed(questiontoblue) != AbstractOracle.USER_ACCEPTED is always true
						if (coregraph.paths.getVertex(questiontoblue) == null)// && redEntry.getValue().isAccept())
						{	
							questionAdded.add(questiontoblue);
						}
					}
				}
			}
		}
		
		
		if (foundKTail)
		{
			return questionAdded;
		}
		return questionAdded;
	}
	
	
	public static Collection<List<Label>> computeLabelsAddedToRedStatesQuestions(LearnerGraph original,StatePair pair)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
//		Visualiser.updateFrame(original,null);
		Map<CmpVertex,List<Label>> stateCover=original.pathroutines.computeShortPathsToAllStatesImproved();				

		assert pair.getQ() != pair.getR();
		assert original.transitionMatrix.containsKey(pair.firstElem);
		assert original.transitionMatrix.containsKey(pair.secondElem);
		Map<CmpVertex,List<CmpVertex>> mergedVertices = original.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(original.getStateNumber()):
				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(original.getStateNumber());
		Configuration shallowCopy = original.config.copy();shallowCopy.setLearnerCloneGraph(false);
		LearnerGraph result = new LearnerGraph(original,shallowCopy);
		assert result.transitionMatrix.containsKey(pair.firstElem);
		assert result.transitionMatrix.containsKey(pair.secondElem);

		long pairScore = original.pairscores.computePairCompatibilityScore_internal(pair,mergedVertices);
		if (pairScore < 0)
			throw new IllegalArgumentException("elements of the pair are incompatible");

//		System.out.println("pair= "+pair+ "  Merged= "+mergedVertices);
		Map<CmpVertex,Collection<Label>> labelsAdded = new TreeMap<CmpVertex,Collection<Label>>();
		
		// make a loop
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:original.transitionMatrix.entrySet())
		{
			for(Entry<Label,CmpVertex> rowEntry:entry.getValue().entrySet())
				if (rowEntry.getValue() == pair.getQ())
				{
					// the transition from entry.getKey() leads to the original blue state, record it to be rerouted.
					result.transitionMatrix.get(entry.getKey()).put(rowEntry.getKey(), pair.getR());		
				}
		}
		
		Set<CmpVertex> ptaVerticesUsed = new HashSet<CmpVertex>();
		Set<Label> inputsUsed = new HashSet<Label>();

		
		// I iterate over the elements of the original graph in order to be able to update the target one.
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:original.transitionMatrix.entrySet())
		{
			CmpVertex vert = entry.getKey();
			Map<Label,CmpVertex> resultRow = result.transitionMatrix.get(vert);// the row we'll update
			if (mergedVertices.containsKey(vert))
			{// there are some vertices to merge with this one.
				Collection<Label> newLabelsAddedToVert = labelsAdded.get(entry.getKey());
				if (newLabelsAddedToVert == null)
				{
					newLabelsAddedToVert = new TreeSet<Label>();
					for(Entry<Label, CmpVertex> l:original.transitionMatrix.get(vert).entrySet())
						newLabelsAddedToVert.add(l.getKey());
					labelsAdded.put(entry.getKey(), newLabelsAddedToVert);
				}

				inputsUsed.clear();inputsUsed.addAll(entry.getValue().keySet());// the first entry is either a "derivative" of a red state or a branch of PTA into which we are now merging more states.
				for(CmpVertex toMerge:mergedVertices.get(vert))
				{// for every input, I'll have a unique target state - this is a feature of PTA
				 // For this reason, every if multiple branches of PTA get merged, there will be no loops or parallel edges.
				// As a consequence, it is safe to assume that each input/target state combination will lead to a new state
				// (as long as this combination is the one _not_ already present from the corresponding red state).
					boolean somethingWasAdded = false;
					for(Entry<Label,CmpVertex> input_and_target:original.transitionMatrix.get(toMerge).entrySet())
						if (!inputsUsed.contains(input_and_target.getKey()))
						{
							// We are adding a transition to state vert with label input_and_target.getKey() and target state input_and_target.getValue();
							resultRow.put(input_and_target.getKey(), input_and_target.getValue());
//							if(input_and_target.getValue().isAccept()==true)
							newLabelsAddedToVert.add(input_and_target.getKey());
							
							inputsUsed.add(input_and_target.getKey());
							ptaVerticesUsed.add(input_and_target.getValue());somethingWasAdded = true;
							// Since PTA is a tree, a tree rooted at ptaVerticesUsed will be preserved in a merged automaton, however 
							// other parts of a tree could be merged into it. In this case, each time there is a fork corresponding to 
							// a step by that other chunk which the current tree cannot follow, that step will end in a tree and a root
							// of that tree will be added to ptaVerticesUsed.
						}
					assert somethingWasAdded : "RedAndBlueToBeMerged was not set correctly at an earlier stage";
				}
			}
		}
		List<Label> question = new LinkedList<Label>();
//		Visualiser.updateFrame(original,null);
		for(Entry<CmpVertex,Collection<Label>> entry:labelsAdded.entrySet())
			for(Label lbl:entry.getValue())
			{
				question = new LinkedList<Label>();
				question.addAll(stateCover.get(entry.getKey()));question.add(lbl);
				if (original.paths.tracePathPrefixClosed(question) != AbstractOracle.USER_ACCEPTED)
				{	
					questionAdded.add(question);
				}
			}

		return questionAdded;
	}
	
	
	public  static Collection<List<Label>> computeLabelsAddedToRedStates(LearnerGraph coregraph, StatePair pair, boolean recursive, boolean loopq)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();
		assert pair.getQ() != pair.getR();
		assert coregraph.transitionMatrix.containsKey(pair.firstElem);
		assert coregraph.transitionMatrix.containsKey(pair.secondElem);
		Map<CmpVertex,List<CmpVertex>> mergedVertices = coregraph.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber()):
				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber());
		Configuration shallowCopy = coregraph.config.copy();shallowCopy.setLearnerCloneGraph(false);

		long pairScore = coregraph.pairscores.computePairCompatibilityScore_internal(pair,mergedVertices);
		if (pairScore < 0)
			return questionAdded;
		
		System.out.println(mergedVertices);
		Set<Label> inputsUsed = new HashSet<Label>();
		
		// I iterate over the elements of the original graph in order to be able to update the target one.
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:coregraph.transitionMatrix.entrySet())
			if ((recursive || entry.getKey() == pair.getR()))// && entry.getKey().getColour() == JUConstants.RED)
			{// only checks for specific state of interest if we are supposed to be non-recursive.			
				CmpVertex vert = entry.getKey();				
				if (mergedVertices.containsKey(vert))
				{// there are some vertices to merge with this one.
					inputsUsed.clear();inputsUsed.addAll(entry.getValue().keySet());// the first entry is either a "derivative" of a red state or a branch of PTA into which we are now merging more states.
					for(CmpVertex toMerge:mergedVertices.get(vert))
					{// for every input, I'll have a unique target state - this is a feature of PTA
					 // For this reason, every if multiple branches of PTA get merged, there will be no loops or parallel edges.
					// As a consequence, it is safe to assume that each input/target state combination will lead to a new state
					// (as long as this combination is the one _not_ already present from the corresponding red state).
						for(Entry<Label,CmpVertex> input_and_target:coregraph.transitionMatrix.get(toMerge).entrySet())
						    if (!inputsUsed.contains(input_and_target.getKey()))
							{
								LinkedList<Label> question = new LinkedList<Label>();
								question.addAll(stateCover.get(entry.getKey()));
								question.add(input_and_target.getKey());
								if (coregraph.paths.getVertex(question)==null)
								{	
									questionAdded.add(question);
								}
							}
					}
				}
			}
		
		return questionAdded;
	}
	
/*	public  static Collection<List<Label>> computeLabelsAddedToRedStatesInconsisteciesImproved(LearnerGraph coregraph, StatePair pair, boolean recursive, boolean loopq, LearnerGraph extendedGraph, Map<CmpVertex, ArrayList<LinkedList<Label>>> collectedFanouts, List<AMEquivalenceClass<CmpVertex, LearnerGraphCachedData>> verticesToMerge)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();
		assert pair.getQ() != pair.getR();
		assert coregraph.transitionMatrix.containsKey(pair.firstElem);
		assert coregraph.transitionMatrix.containsKey(pair.secondElem);
		if(pair.getQ().isAccept()==false && pair.getR().isAccept()==false)
			return questionAdded;

		Set<Label> inputsUsed = new HashSet<Label>();
		
		Set<CmpVertex> affectedVerticesInMergedGraph = new LinkedHashSet<CmpVertex>();
		for(AMEquivalenceClass<CmpVertex,LearnerGraphCachedData> eqClass:verticesToMerge)
			if (eqClass.getStates().size() > 1 && eqClass.getMergedVertex().isAccept())
			{
				affectedVerticesInMergedGraph.add(eqClass.getMergedVertex());
				
			}
				// add labels from the merged node
//				inputsUsed.clear();
//				inputsUsed.addAll(coregraph.transitionMatrix.get(eqClass.getMergedVertex()).keySet());// the first entry is either a "derivative" of a red state or a branch of PTA into which we are now merging more states.

//				System.out.println(pair);
				for(CmpVertex mergednode:affectedVerticesInMergedGraph)
				{
					
					 * collectedFanouts is Map of merged vertices to the labels that are caused inconsistency
					 *  
					 
					
					for(LinkedList<Label> l:collectedFanouts.get(mergednode))
				    {		
						LinkedList<Label> question = new LinkedList<Label>();
						question.addAll(stateCover.get(mergednode));
						for(Label label:l)
						{
							question.add(label);
							if(coregraph.paths.getVertex(question)!=null)
							{
								if(!coregraph.paths.getVertex(question).isAccept())
								{
									question.clear();
									break;
								}		
							}
						}
						if(question.size() > 0 && coregraph.paths.getVertex(question)==null)
						{
							questionAdded.add(question);
//							System.out.println("question generation:"+question);
						}
					}						
				}
		
		return questionAdded;
	}*/
	
	/** 
	 * It computes queries based on labels that would be added to the merged (red) nodes from the (blue) nodes.
	 * 
	 * @param pair
	 * @param graph is current graph.
	 * @param MarkovGraph is graph with extension based on Markov predictions.
	 * @param verticesToMerge are vertices that would be merged.
	 * @param checkInconsistecy 
	 * @param markov 
	 * @param merged 
	 * @return collection of queries.
	 */
	
	public  static Collection<List<Label>> computeCoreQueries(StatePair pair, LearnerGraph coregraph, LearnerGraph extendedGraph, boolean recursive, List<AMEquivalenceClass<CmpVertex, LearnerGraphCachedData>> verticesToMerge, boolean checkInconsistecy, int markovchunk, LearnerGraph merged)
	{
		Collection<List<Label>> questionAdded = new HashSet<List<Label>>();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();

		assert pair.getQ() != pair.getR();
		assert coregraph.transitionMatrix.containsKey(pair.firstElem);
		assert coregraph.transitionMatrix.containsKey(pair.secondElem);
		if(pair.getQ().isAccept()==false && pair.getR().isAccept()==false)
			return questionAdded;
		
		// Map Merged node to its states
		Map<CmpVertex,ArrayList<CmpVertex>> MapMergedRed = new TreeMap<CmpVertex,ArrayList<CmpVertex>>(); 
		int n=0;
		for(AMEquivalenceClass<CmpVertex,LearnerGraphCachedData> eqClass:verticesToMerge)
			if(eqClass.getStates().size() > 1 && eqClass.getMergedVertex().isAccept())
			if (recursive || eqClass.getStates().contains(pair.getR()))
			{
				n++;
				ArrayList<CmpVertex> StatesToMergeWithRed=new ArrayList<CmpVertex>();
				
				/*if(eqClass.getMergedVertex()==pair.getR())
				{
					assert eqClass.getMergedVertex().getColour()!=JUConstants.BLUE;
				}*/
				for(CmpVertex current:eqClass.getStates())
				{
					if(!current.getStringId().equals(eqClass.getMergedVertex().getStringId()))
					{
						StatesToMergeWithRed.add(current);
					}
				}
				MapMergedRed.put(eqClass.getMergedVertex(), StatesToMergeWithRed);
			}
		assert n==MapMergedRed.size();

		if(checkInconsistecy)
		{
			for(CmpVertex mergednode:MapMergedRed.keySet())
			{
				Set<Label> inputsUsed = new HashSet<Label>();			
				inputsUsed.clear();
				inputsUsed.addAll(coregraph.transitionMatrix.get(mergednode).keySet());
				for(CmpVertex toMerge:MapMergedRed.get(mergednode))
				{
					for(Entry<Label,CmpVertex> input_and_target:coregraph.transitionMatrix.get(toMerge).entrySet())
					    if (!inputsUsed.contains(input_and_target.getKey()))
						{
							LinkedList<Label> question = new LinkedList<Label>();
							question.addAll(stateCover.get(mergednode));
							question.add(input_and_target.getKey());
							// not predicted
							if (coregraph.paths.getVertex(question)==null && extendedGraph.transitionMatrix.get(mergednode).get(input_and_target.getKey())==null)
							{	
								questionAdded.add(question);
							}
							//conflict in prediction
							else if (coregraph.paths.getVertex(question)==null && extendedGraph.transitionMatrix.get(mergednode).get(input_and_target.getKey()).isAccept()!=input_and_target.getValue().isAccept())  
							{
								questionAdded.add(question);
							}
//							else if (coregraph.paths.getVertex(question)==null &&  extendedGraph.transitionMatrix.get(mergednode).get(input_and_target.getKey()).isAccept()==input_and_target.getValue().isAccept() && question.size() < markovchunk)  
//							{
//								questionAdded.add(question);
//							}							
//							else
//							{
//								System.out.println(question + " it drops"+ " -> "+input_and_target.getValue().isAccept() + " Ml- "+ markov.computePredictionMatrix() + " p"+pair);
//							}
						}
				}			
			}
		}
		
		else
		{
		    for(CmpVertex mergednode:MapMergedRed.keySet())
			{
				Set<Label> inputsUsed = new HashSet<Label>();			
				inputsUsed.clear();
				inputsUsed.addAll(coregraph.transitionMatrix.get(mergednode).keySet());
				for(CmpVertex toMerge:MapMergedRed.get(mergednode))
				{
					for(Entry<Label,CmpVertex> input_and_target:coregraph.transitionMatrix.get(toMerge).entrySet())
					    if (!inputsUsed.contains(input_and_target.getKey()))
						{
							LinkedList<Label> question = new LinkedList<Label>();
							question.addAll(stateCover.get(mergednode));
							question.add(input_and_target.getKey());
							if (coregraph.paths.getVertex(question)==null )
							{	
								questionAdded.add(question);
							}
						}
				}			
			}
		}
		
		
		
		// with inconsistencies
		/*for(CmpVertex mergednode:affectedVerticesInMergedGraph)
		{
			Set<Label> inputsUsed = new HashSet<Label>();			
			inputsUsed.clear();
			inputsUsed.addAll(coregraph.transitionMatrix.get(mergednode).keySet());
			for(CmpVertex toMerge:allstatestomergedwith.get(mergednode))
			{
				for(Entry<Label,CmpVertex> input_and_target:coregraph.transitionMatrix.get(toMerge).entrySet())
				    if (!inputsUsed.contains(input_and_target.getKey()) && collectedInocnsisteciesFanouts.get(mergednode).contains(input_and_target.getKey()))
					{
						LinkedList<Label> question = new LinkedList<Label>();
						question.addAll(stateCover.get(mergednode));
						question.add(input_and_target.getKey());
						if (coregraph.paths.getVertex(question)==null)
						{	
							questionAdded.add(question);
						}
					}
			}			
		}*/
					
		/*for(CmpVertex mergednode:affectedVerticesInMergedGraph)
		{								
			for(Label l:collectedInocnsisteciesFanouts.get(mergednode))
		    {		
				LinkedList<Label> question = new LinkedList<Label>();
				question.addAll(stateCover.get(mergednode));						
				question.add(l);
				if(coregraph.paths.getVertex(question)==null)
					questionAdded.add(question);				
			}
		}*/
		return questionAdded;
	}
	
	public  static Collection<List<Label>> computeLabelsAddedToRedStatesInconsisteciesfinal(LearnerGraph coregraph, StatePair pair, boolean recursive, LearnerGraph extendedGraph, Map<CmpVertex, Set<Label>> collectedFanouts)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();
		assert pair.getQ() != pair.getR();
		assert coregraph.transitionMatrix.containsKey(pair.firstElem);
		assert coregraph.transitionMatrix.containsKey(pair.secondElem);
		Map<CmpVertex,List<CmpVertex>> mergedVertices = coregraph.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber()):
				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber());
		Configuration shallowCopy = coregraph.config.copy();shallowCopy.setLearnerCloneGraph(false);

		long pairScore = coregraph.pairscores.computePairCompatibilityScore_bluefringe(pair, mergedVertices);
		if (pairScore < 0)
			return questionAdded;
		
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:coregraph.transitionMatrix.entrySet())
			if ((recursive || entry.getKey() == pair.getR()))
			{				
				CmpVertex vert = entry.getKey();
				
				/*if (mergedVertices.containsKey(vert) && vert.isAccept())
				{
					for(Label l:collectedFanouts.get(vert))
				    {
						LinkedList<Label> question = new LinkedList<Label>();
						question.addAll(stateCover.get(entry.getKey()));
						question.add(l);
						if (coregraph.paths.getVertex(question)==null)// && extendedGraph.transitionMatrix.get(entry.getKey()).get(l)==null)
						{	
							questionAdded.add(question);
						}
					}									
				}*/
				
				if(mergedVertices.get(pair.getR())==null)
				{
					System.out.println("MergedVertices: "+pair.getR() + " vertices "+mergedVertices);
				}
				
				Set<Label> inputsUsed = new HashSet<Label>();
				if (mergedVertices.containsKey(vert) && vert.isAccept())
				{
					inputsUsed.clear();inputsUsed.addAll(entry.getValue().keySet());
					for(CmpVertex toMerge:mergedVertices.get(vert))
					{
						for(Entry<Label,CmpVertex> input_and_target:coregraph.transitionMatrix.get(toMerge).entrySet())
						    if (!inputsUsed.contains(input_and_target.getKey()))
							{
								LinkedList<Label> question = new LinkedList<Label>();
								question.addAll(stateCover.get(entry.getKey()));
								question.add(input_and_target.getKey());
								if (coregraph.paths.getVertex(question)==null && extendedGraph.transitionMatrix.get(entry.getKey()).get(input_and_target.getKey())==null)
								{	
									questionAdded.add(question);
								}
							}
					}
				}
			}
		
		return questionAdded;
	}
	
	public  static Collection<List<Label>> computeLabelsAddedToRedStatesInconsistecies(LearnerGraph coregraph, StatePair pair, boolean recursive, LearnerGraph extendedGraph, Map<CmpVertex, Set<Label>> collectedFanouts)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();
		assert pair.getQ() != pair.getR();
		assert coregraph.transitionMatrix.containsKey(pair.firstElem);
		assert coregraph.transitionMatrix.containsKey(pair.secondElem);
		Map<CmpVertex,List<CmpVertex>> mergedVertices = coregraph.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber()):
				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber());
		Configuration shallowCopy = coregraph.config.copy();shallowCopy.setLearnerCloneGraph(false);

		long pairScore = coregraph.pairscores.computePairCompatibilityScore_internal(pair,mergedVertices);
		if (pairScore < 0)
			return questionAdded;

		Set<Label> inputsUsed = new HashSet<Label>();
		
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:coregraph.transitionMatrix.entrySet())
			if ((recursive || entry.getKey() == pair.getR()))
			{				
				CmpVertex vert = entry.getKey();
				if (mergedVertices.containsKey(vert) && vert.isAccept())
				{
					inputsUsed.clear();inputsUsed.addAll(entry.getValue().keySet());
					for(Label l:collectedFanouts.get(vert))
				    {
						LinkedList<Label> question = new LinkedList<Label>();
						question.addAll(stateCover.get(entry.getKey()));
						question.add(l);
						if (coregraph.paths.getVertex(question)==null && extendedGraph.transitionMatrix.get(entry.getKey()).get(l)==null)
						{	
							questionAdded.add(question);
						}
					}									
				}
			}
		
		return questionAdded;
	}
	
	public  static Collection<List<Label>> computeScoreSiccoqqq(LearnerGraph coregraph, StatePair pair, boolean recursive)
	{
		Collection<List<Label>> questionAdded = new ArrayList<List<Label>>();
		Map<CmpVertex,List<Label>> stateCover=coregraph.pathroutines.computeShortPathsToAllStates();		
		assert pair.getQ() != pair.getR();
		assert coregraph.transitionMatrix.containsKey(pair.firstElem);
		assert coregraph.transitionMatrix.containsKey(pair.secondElem);
		Map<CmpVertex,List<CmpVertex>> mergedVertices = coregraph.config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?
				new ArrayMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber()):
				new HashMapWithSearch<CmpVertex,List<CmpVertex>>(coregraph.getStateNumber());
		Configuration shallowCopy = coregraph.config.copy();shallowCopy.setLearnerCloneGraph(false);

		long pairScore = coregraph.pairscores.computePairCompatibilityScore_internal(pair,mergedVertices);
//		if (pairScore < 0)
//			return -1;

		Set<Label> inputsUsed = new HashSet<Label>();

		// I iterate over the elements of the original graph in order to be able to update the target one.
		for(Entry<CmpVertex,Map<Label,CmpVertex>> entry:coregraph.transitionMatrix.entrySet())
			if ( (recursive || entry.getKey() == pair.getR()) && entry.getKey().getColour() == JUConstants.RED)
			{// only checks for specific state of interest if we are supposed to be non-recursive.
				CmpVertex vert = entry.getKey();
				if (mergedVertices.containsKey(vert))
				{// there are some vertices to merge with this one.
					inputsUsed.clear();inputsUsed.addAll(entry.getValue().keySet());// the first entry is either a "derivative" of a red state or a branch of PTA into which we are now merging more states.
					for(CmpVertex toMerge:mergedVertices.get(vert))
					{// for every input, I'll have a unique target state - this is a feature of PTA
					 // For this reason, every if multiple branches of PTA get merged, there will be no loops or parallel edges.
					// As a consequence, it is safe to assume that each input/target state combination will lead to a new state
					// (as long as this combination is the one _not_ already present from the corresponding red state).
						for(Entry<Label,CmpVertex> input_and_target:coregraph.transitionMatrix.get(toMerge).entrySet())
							if (input_and_target.getValue().isAccept() && !inputsUsed.contains(input_and_target.getKey()))
//						    if (!inputsUsed.contains(input_and_target.getKey()))
							{
								LinkedList<Label> question = new LinkedList<Label>();
								question.addAll(stateCover.get(entry.getKey()));question.add(input_and_target.getKey());
								if (coregraph.paths.tracePathPrefixClosed(question) != AbstractOracle.USER_ACCEPTED)
								{	
									questionAdded.add(question);
								}
							}
					}
				}
			}
		
		return questionAdded;
	}
	
	public static void extendWithLabel(LearnerGraph what, CmpVertex prevState, boolean isAccept, Label input)
	{
		CmpVertex newVertex = AbstractLearnerGraph.generateNewCmpVertex(what.nextID(isAccept),what.config);
		assert !what.transitionMatrix.containsKey(newVertex);
		newVertex.setAccept(isAccept);
		what.transitionMatrix.put(newVertex, what.createNewRow());
		what.addTransition(what.transitionMatrix.get(prevState),input,newVertex);
	}
	public static List<List<Label>> FilterQueries(List<List<Label>> questionsFor, LearnerGraph extendedGraph, LearnerGraph merged, MarkovModel markov)
	{
		List<List<Label>> questionAddedAfterFilter = new ArrayList <List<Label>>();
		for(List<Label> qs:questionsFor)
		{
			List<Trace> elems=MarkovModel.splitTrace(new Trace(qs, false), markov.getChunkLen());
			for(Trace t:elems)
				if (markov.markovMatrix.getPrediction(t.getList()).prediction != MarkovOutcome.positive)
				{
					questionAddedAfterFilter.add(qs);break;
				}
		}
		
		return questionAddedAfterFilter;
	}
	
	public static List<List<Label>> FilterQueries2(List<List<Label>>  questionsFor, LearnerGraph extendedGraph, LearnerGraph merged)
	{ 
		List<List<Label>> questionAddedAfterFilter = new ArrayList <List<Label>>();
		

		for(List<Label> qs:questionsFor)
		{			
			if (extendedGraph.getVertex(qs)==null)  
			{
				questionAddedAfterFilter.add(qs);
			}
			else
			{
			    if (extendedGraph.getVertex(qs).isAccept()!=merged.getVertex(qs).isAccept())  
				{
					questionAddedAfterFilter.add(qs);
				}
			    else
				{
					// Question is predicted correctly
				}
			}
			
		}		
		return questionAddedAfterFilter;
	}

	
	public static List<List<Label>> FilterQueries3(List<List<Label>> questionsFor, LearnerGraph extendedGraph, LearnerGraph merged)
	{ 
		List<List<Label>> questionAddedAfterFilter = new ArrayList <List<Label>>();

		for(List<Label> qs:questionsFor)
		{
			if (extendedGraph.getVertex(qs)==null)  
			{
				questionAddedAfterFilter.add(qs);
			}
			else if(merged.getVertex(qs)!=null)
			{
			    if (extendedGraph.getVertex(qs).isAccept()!=merged.getVertex(qs).isAccept())  
				{
					questionAddedAfterFilter.add(qs);
				}
			    else
				{
					// Question is predicted correctly
				}
			}
			
		}		
		return questionAddedAfterFilter;
	}
	



}
