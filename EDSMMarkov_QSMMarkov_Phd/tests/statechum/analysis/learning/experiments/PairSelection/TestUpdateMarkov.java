package statechum.analysis.learning.experiments.PairSelection;

import static statechum.analysis.learning.rpnicore.FsmParser.buildLearnerGraph;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.Map.Entry;

import org.junit.Assert;
import org.junit.Test;

import statechum.Configuration;
import statechum.JUConstants;
import statechum.Label;
import statechum.Configuration.QuestionGeneratorKind;
import statechum.Configuration.STATETREE;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.analysis.learning.MarkovClassifier;
import statechum.analysis.learning.MarkovModel;
import statechum.analysis.learning.StatePair;
import statechum.analysis.learning.Visualiser;
import statechum.analysis.learning.MarkovModel.MarkovOutcome;
import statechum.analysis.learning.experiments.PairSelection.MarkovQuestionGeneration;
import statechum.analysis.learning.rpnicore.AMEquivalenceClass;
import statechum.analysis.learning.rpnicore.LearnerGraph;
import statechum.analysis.learning.rpnicore.LearnerGraphCachedData;
import statechum.analysis.learning.rpnicore.MergeStates;
import statechum.analysis.learning.rpnicore.TestFSMAlgo;
import statechum.analysis.learning.rpnicore.Transform;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;

public class TestUpdateMarkov {
	
	ConvertALabel converter = null;
	Configuration config = null;
	public TestUpdateMarkov()
	{
		config = Configuration.getDefaultConfiguration().copy();
		converter = config.getTransitionMatrixImplType() == STATETREE.STATETREE_ARRAY?new Transform.InternStringLabel():null;	
	}
	
	@Test
	public final void testQuestions1()
	{
		int chunkLen=3;
		LearnerGraph pta = buildLearnerGraph("A-b->B-a->C-a->D-d->H / D-e->F-b->K-n->L", "testQuestions1",config,converter);
		final MarkovModel m= new MarkovModel(chunkLen,true,true,false);
		new MarkovClassifier(m, pta).updateMarkov(true);
		Map<String,MarkovOutcome> map = new TreeMap<String,MarkovOutcome>();
		for(Entry<List<Label>, MarkovOutcome> entry:m.computePredictionMatrix().entrySet())
			map.put(entry.getKey().toString(), entry.getValue()); 
		System.out.println(map);
		Assert.assertEquals("{[a, a, d]=(+), [a, a, e]=(+), [a, e, b]=(+), [b, a, a]=(+), [e, b, n]=(+)}",
				map.toString());
		LearnerGraph questionpta = buildLearnerGraph("A-b->B-a->C-a->D-d->H / D-e->F-a->Q-m->L", "testQuestions1",config,converter);
		Visualiser.updateFrame(questionpta, null);

		new MarkovClassifier(m,questionpta).updateMarkov(true);
		map = new TreeMap<String,MarkovOutcome>();
		for(Entry<List<Label>, MarkovOutcome> entry:m.computePredictionMatrix().entrySet())
			map.put(entry.getKey().toString(), entry.getValue()); 
		System.out.println(map);
		Assert.assertEquals("{[a, a, d]=(+), [a, a, e]=(+), [a, e, a]=(+), [a, e, b]=(+), [b, a, a]=(+), [e, a, m]=(+), [e, b, n]=(+)}",
				map.toString());

	}
	
	
	@Test
	public final void testQuestions2()
	{
		int chunkLen=3;
		LearnerGraph pta = buildLearnerGraph("A-Load->B-Close->D-Load->K / B-Edit->C-Edit->G-Save->H-Close->I/ C-Save->E/ I-Load->M/ E-Edit->N/ H-Edit->O-Edit->L", "testQuestions13",config,converter);
		final MarkovModel m= new MarkovModel(chunkLen,true,true,false);
//		Visualiser.updateFrame(pta, null);

		new MarkovClassifier(m, pta).updateMarkov(true);
		Map<String,MarkovOutcome> map = new TreeMap<String,MarkovOutcome>();
		for(Entry<List<Label>, MarkovOutcome> entry:m.computePredictionMatrix().entrySet())
			map.put(entry.getKey().toString(), entry.getValue()); 
		System.out.println(map);
		Assert.assertEquals("{[Edit, Edit, Save]=(+), [Edit, Save, Close]=(+), [Edit, Save, Edit]=(+), [Load, Close, Load]=(+), [Load, Edit, Edit]=(+), [Load, Edit, Save]=(+), [Save, Close, Load]=(+), [Save, Edit, Edit]=(+)}",
				map.toString());
		LearnerGraph questionpta = buildLearnerGraph("A-Laod->B-Close->C-Edit-#D / B-Edit->Q-Close-#L / Q-Load-#Z", "testQuestions1",config,converter);
		Visualiser.updateFrame(questionpta, null);

		new MarkovClassifier(m,questionpta).updateMarkov(true);
		map = new TreeMap<String,MarkovOutcome>();
		for(Entry<List<Label>, MarkovOutcome> entry:m.computePredictionMatrix().entrySet())
			map.put(entry.getKey().toString(), entry.getValue()); 
		System.out.println(map);
		Assert.assertEquals("{[Edit, Edit, Save]=(+), [Edit, Save, Close]=(+), [Edit, Save, Edit]=(+), [Laod, Close, Edit]=(-), [Laod, Edit, Close]=(-), [Laod, Edit, Load]=(-), [Load, Close, Load]=(+), [Load, Edit, Edit]=(+), [Load, Edit, Save]=(+), [Save, Close, Load]=(+), [Save, Edit, Edit]=(+)}",
				map.toString());

	}
	
	
}
