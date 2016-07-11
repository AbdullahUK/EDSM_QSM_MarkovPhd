package statechum.analysis.learning.rpnicore;

import static statechum.analysis.learning.rpnicore.FsmParser.buildLearnerGraph;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.junit.Assert;
import org.junit.Test;

import statechum.Configuration;
import statechum.Label;
import statechum.Configuration.QuestionGeneratorKind;
import statechum.Configuration.STATETREE;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.analysis.learning.MarkovClassifier;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.experiments.PairSelection.MarkovQuestionGeneration;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;

public class TestCoreQuestionGeneration {
	
	ConvertALabel converter = null;
	Configuration config = null;
	public TestCoreQuestionGeneration()
	{
		config = Configuration.getDefaultConfiguration().copy();
		converter = config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?new Transform.InternStringLabel():null;	
	}
	
	@Test
	public final void testQuestions1()
	{
		config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
		LearnerGraph graph = buildLearnerGraph("A-b->B-a->C-a->D-d->H / D-e->F", "testQuestions1",config,converter);
		StatePair pair = new StatePair(graph.findVertex("C"),graph.findVertex("B"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
//		Visualiser.updateFrame(graph, merged);
		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);						
		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"b","d"},new String[]{"b","e"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions2()
	{
		config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
		LearnerGraph graph = buildLearnerGraph("A-a->B / B-b->C-b->D / C-g->E / B-c->F-d->G / F-f->H", "testQuestions2",config,converter);
		StatePair pair = new StatePair(graph.findVertex("F"),graph.findVertex("C"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
//		Visualiser.updateFrame(graph, merged);		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);	
		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","b","d"},new String[]{"a","b","f"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions3()
	{
		config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-a->E-b->F/E-d->G", "testQuestions3",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
//		Visualiser.updateFrame(graph, merged);
		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);						
		
		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","b","b"},new String[]{"a","b","d"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	
	@Test
	public final void testQuestions4()
	{
		config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-b->E-b->F/E-d->G/E-e->H", "testQuestions4",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
//		Visualiser.updateFrame(graph, merged);
		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);					

		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","b","d"},new String[]{"a","b","e"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	
	@Test
	public final void testQuestions5()
	{
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-b->E-b->F/E-d->G/E-e->H-a->I/F-a->L/G-h->M", "testQuestions5",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
		Visualiser.updateFrame(graph, merged);
		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);						
		
		//		System.out.println(qs);
		Assert.assertEquals(3,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","b","d"},new String[]{"a","b","e"},new String[]{"a","b","a"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions6()
	{
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-b->E-b->F-d->G", "testQuestions6",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
		Visualiser.updateFrame(graph, merged);
		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);						
		
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","b","d"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	
	@Test
	public final void testQuestions7()
	{
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-b->E-b->F-b->G", "testQuestions7",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
		Visualiser.updateFrame(graph, merged);		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);	
		Assert.assertEquals(0,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{},config,converter);
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	
	@Test
	public final void testQuestions8()
	{
		config.setQuestionGenerator(QuestionGeneratorKind.DUPONT);
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-b->E-b->F/E-d->G/E-e->H-a->I/F-a->L/G-h->M/E-a->D", "testQuestions8",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
		Visualiser.updateFrame(graph, merged);
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);						

		Assert.assertEquals(3,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","b","a"},new String[]{"a","b","d"},new String[]{"a","b","e"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	
	@Test
	public final void testQuestions9()
	{
		LearnerGraph graph = buildLearnerGraph("A-a->B-b->D / A-b->C-c->D-b->E-b->F/E-d->G/E-e->H-a->I/F-a->L/G-h->M/E-a->D-a->B", "testQuestions9",config,converter);
		StatePair pair = new StatePair(graph.findVertex("E"),graph.findVertex("D"));
		LearnerGraph merged = MergeStates.mergeAndDeterminize_general(graph, pair);
		Visualiser.updateFrame(graph, merged);
		
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		graph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge);
		LearnerGraph merged1=MergeStates.mergeCollectionOfVerticesNoUpdateOfAuxiliaryInformation(graph, verticesToMerge);
		Set<List<Label>> qs = (Set<List<Label>>) MarkovQuestionGeneration.computeCoreQueries(pair, graph, graph, true, verticesToMerge,false, 2, merged1);						
		
		Assert.assertEquals(3,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"a","a"},new String[]{"a","d"},new String[]{"a","e"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
			assert merged.getVertex(ex)!=null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
}
