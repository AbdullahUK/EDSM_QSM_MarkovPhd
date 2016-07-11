package statechum.analysis.learning.rpnicore;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import statechum.Configuration;
import statechum.Label;
import statechum.Configuration.STATETREE;
import statechum.Configuration.ScoreMode;
import statechum.DeterministicDirectedSparseGraph.CmpVertex;
import statechum.DeterministicDirectedSparseGraph.VertexID;
import statechum.analysis.learning.AbstractOracle;
import statechum.analysis.learning.PairScore;
import statechum.analysis.learning.rpnicore.Transform.ConvertALabel;

public class DebugRepeatedQuestion {

	public static void main(String[] args) throws IOException {
		Configuration config = Configuration.getDefaultConfiguration().copy();
		config.setAskQuestions(true);
		config.setDebugMode(false);
		config.setGdLowToHighRatio(0.7);
		config.setRandomPathAttemptFudgeThreshold(1000);
		config.setTransitionMatrixImplType(STATETREE.STATETREE_ARRAY);
		config.setLearnerScoreMode(ScoreMode.GENERAL);
		ConvertALabel converter = new Transform.InternStringLabel();					
		LearnerGraph coregraph = new LearnerGraph(config);AbstractPersistence.loadGraph("rq_Tentative", coregraph, converter);
		LearnerGraph hardfacts = new LearnerGraph(config);AbstractPersistence.loadGraph("rq_HardFacts", hardfacts, converter);
		
		PairScore pair = new PairScore(coregraph.findVertex(VertexID.parseID("P5428")),coregraph.findVertex(VertexID.parseID("P1002")),0,0);
		List<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>> verticesToMerge = new LinkedList<AMEquivalenceClass<CmpVertex,LearnerGraphCachedData>>();//coregraph.getStateNumber()+1);// to ensure arraylist does not reallocate when we fill in the last element
		System.out.println(coregraph.pairscores.computePairCompatibilityScore_general(pair, null, verticesToMerge));
		
		final LearnerGraph temp = MergeStates.mergeAndDeterminize_general(coregraph, pair);
		Collection<List<Label>> questions = new LinkedList<List<Label>>();
		questions = ComputeQuestions.RecomputeQS(pair, coregraph,temp, null);
		System.out.println("questions: "+questions.size());
		Iterator<List<Label>> questionIt = questions.iterator();
		while (questionIt.hasNext())
		{
			List<Label> question = questionIt.next();
			if (hardfacts.paths.tracePathPrefixClosed(question) == AbstractOracle.USER_ACCEPTED) {
				System.out.println("question already answered: "+question);
				System.out.println(coregraph.paths.tracePathPrefixClosed(question));
			}
			
		}
	}

}
