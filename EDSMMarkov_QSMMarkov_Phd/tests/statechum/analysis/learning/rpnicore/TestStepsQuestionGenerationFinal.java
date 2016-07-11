package statechum.analysis.learning.rpnicore;

import static statechum.analysis.learning.rpnicore.FsmParser.buildLearnerGraph;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import org.junit.Assert;
import org.junit.Test;

import statechum.Configuration;
import statechum.JUConstants;
import statechum.Label;
import statechum.Configuration.QuestionGeneratorKind;
import statechum.Configuration.STATETREE;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.analysis.learning.PairScore;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.experiments.PairSelection.MarkovQuestionGeneration;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;

public class TestStepsQuestionGenerationFinal {
	
	ConvertALabel converter = null;
	Configuration config = null;
	public TestStepsQuestionGenerationFinal()
	{
		config = Configuration.getDefaultConfiguration().copy();
		converter = config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?new Transform.InternStringLabel():null;	
	}
	
	@Test
	public final void testQuestions1()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-b->B-a->C-a->D-d->H / D-e->F", "testQuestions1",config,converter);
		StatePair pair = new StatePair(graph.findVertex("C"),graph.findVertex("B"));
		graph.findVertex("A").setColour(JUConstants.RED);
	    pair.getR().setColour(JUConstants.RED);
	    pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));						
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"b","a","a","a"}
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
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-b->B-a->C-a->D-d->H / D-e->F / C-d->G", "testQuestions2",config,converter);
		StatePair pair = new StatePair(graph.findVertex("C"),graph.findVertex("B"));
		graph.findVertex("A").setColour(JUConstants.RED);
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"b","a","a","a"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions3()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-b->B-a->C-a->D-d->H / D-e->F / C-d->G-k->M", "testQuestions3",config,converter);
		StatePair pair = new StatePair(graph.findVertex("C"),graph.findVertex("B"));
		graph.findVertex("A").setColour(JUConstants.RED);
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"b","a","a","a"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	

	@Test
	public final void testQuestions4()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-Load->B-Close->D-Load->K / B-Edit->C-Edit->G-Save->H-Close->I/ C-Save->E/ I-Load->M/ E-Edit->N/ H-Edit->O-Edit->L", "testQuestions13",config,converter);
		StatePair pair = new StatePair(graph.findVertex("G"),graph.findVertex("C"));
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"Load","Edit","Edit","Edit"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions5()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-Load->B-Close->D-Load->K / B-Edit->C-Edit->G-Save->H-Close->I/ C-Save->E/ I-Load->M/ E-Edit->N-Save->P/ H-Edit->O-Edit->L", "testQuestions5",config,converter);
		StatePair pair = new StatePair(graph.findVertex("G"),graph.findVertex("C"));
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"Load","Edit","Edit","Edit"},
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions6()
	{
		int numberofsteps =1;
		LearnerGraph graph = buildLearnerGraph("A-Load->B-Close->D-Load->K / B-Edit->C-Edit->G-Save->H-Close->I/ C-Save->E/ I-Load->M/ E-Edit->N-Save->P/ H-Edit->O-Edit->L", "testQuestions6",config,converter);
		StatePair pair = new StatePair(graph.findVertex("G"),graph.findVertex("C"));
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(1,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"Load","Edit","Edit","Edit"},
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions7()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-b->B-a->C-a->D-e->F / C-d->G-k->M", "testQuestions7",config,converter);
		StatePair pair = new StatePair(graph.findVertex("C"),graph.findVertex("B"));
		graph.findVertex("A").setColour(JUConstants.RED);
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"b","a","a","a"},new String[]{"b","a","a","d"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions8()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-Load->B-Close->D-Load->K / B-Edit->C-Edit->G-Save->H-Close->I/ C-Save->E/ I-Load->M/ E-Edit->N-Save->P/ H-Edit->O-Edit->L/ G-Edit->T", "testQuestions8",config,converter);
		StatePair pair = new StatePair(graph.findVertex("G"),graph.findVertex("C"));
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));
		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"Load","Edit","Edit","Edit","Edit"},{"Load","Edit","Edit","Edit","Save"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
	
	@Test
	public final void testQuestions9()
	{
		int numberofsteps =2;
		LearnerGraph graph = buildLearnerGraph("A-Load->B-Close->D-Load->K / B-Edit->C-Edit->G/ D-Save-#N", "testQuestions8",config,converter);
		PairScore pair = new PairScore(graph.findVertex("C"),graph.findVertex("B"),0,0);
		pair.getR().setColour(JUConstants.RED);
		pair.getQ().setColour(JUConstants.BLUE);
		Visualiser.updateFrame(graph, null);
		Set<List<Label>> qs =  new HashSet<List<Label>>();
//		qs.addAll(MarkovQuestionGeneration.computeOneStep(pair, graph, graph, false));
//		qs.addAll(MarkovQuestionGeneration.computeScoreSiccoqqq(graph, pair, false));
		qs.addAll(MarkovQuestionGeneration.computeKtailQueriesimproved(graph, pair, numberofsteps));

		Assert.assertEquals(2,qs.size());
		Set<List<Label>> expected = TestFSMAlgo.buildSet(new String[][]{
				new String[]{"Load","Edit","Edit","Edit","Edit"},{"Load","Edit","Edit","Edit","Save"}
				},config,converter);
		for( List<Label> ex:expected)
		{
			assert graph.getVertex(ex)==null;
		}
		Set<List<Label>> actual = new LinkedHashSet<List<Label>>();actual.addAll(qs);
		Assert.assertEquals(expected,actual);
	}
}
