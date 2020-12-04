package org.jcfgonc.graphisomorphism;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.IntStream;

import com.githhub.aaronbembenek.querykb.Conjunct;
import com.githhub.aaronbembenek.querykb.KnowledgeBase;
import com.githhub.aaronbembenek.querykb.KnowledgeBase.KnowledgeBaseBuilder;
import com.githhub.aaronbembenek.querykb.Query;

import frames.FrameReadWrite;
import frames.SemanticFrame;
import graph.GraphAlgorithms;
import graph.StringEdge;
import graph.StringGraph;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import structures.MapOfList;

public class IsomorphismFinderLauncher {
	public static HashMap<String, String> createConceptToVariableMapping(StringGraph pattern) {
		Set<String> vertexSet = pattern.getVertexSet();
		HashMap<String, String> conceptToVariable = new HashMap<>(vertexSet.size() * 2);
		int varCounter = 0;
		for (String concept : vertexSet) {
			String varName = "X" + varCounter;
			conceptToVariable.put(concept, varName);
			varCounter++;
		}
		return conceptToVariable;
	}

	/**
	 * creates a querykb conjunction to be used as a query using the given variable<=>variable mapping
	 * 
	 * @param pattern
	 * @param conceptToVariable
	 * @return
	 */
	public static ArrayList<Conjunct> createConjunctionFromStringGraph(final StringGraph pattern, final HashMap<String, String> conceptToVariable) {

		ArrayList<Conjunct> conjunctList = new ArrayList<>();

		// create the query as a conjunction of terms
		for (StringEdge edge : pattern.edgeSet()) {

			String edgeLabel = edge.getLabel();
			String sourceVar = edge.getSource();
			String targetVar = edge.getTarget();
			if (conceptToVariable != null) {
				sourceVar = conceptToVariable.get(sourceVar);
				targetVar = conceptToVariable.get(targetVar);
			}
			conjunctList.add(Conjunct.make(edgeLabel, sourceVar, targetVar));
		}
		return conjunctList;
	}

	public static KnowledgeBase buildKnowledgeBase(StringGraph kbGraph) {
		KnowledgeBaseBuilder kbb = new KnowledgeBaseBuilder();
		// Ticker ticker = new Ticker();

		for (StringEdge edge : kbGraph.edgeSet()) {
			String label = edge.getLabel();
			String source = edge.getSource();
			String target = edge.getTarget();
			kbb.addFact(label, source, target);
		}

		KnowledgeBase kb = kbb.build();
		// System.out.println("build took " + ticker.getElapsedTime() + " s");
		return kb;
	}

	public static void main(String[] args) throws IOException, InterruptedException {
		// read graphs
		String framesPath = "../PatternMiner/results/resultsV22.csv";
		ArrayList<SemanticFrame> frames = FrameReadWrite.readPatternFrames(framesPath);

		// MapOfList<Integer, StringGraph> graphsPerVertices = new MapOfList<>();
		MapOfList<Object2IntOpenHashMap<String>, StringGraph> graphGroups = new MapOfList<Object2IntOpenHashMap<String>, StringGraph>();

		// organize graphs in groups according to the relations' histograms
		for (SemanticFrame frame : frames) {
			StringGraph graph = frame.getGraph();
			Object2IntOpenHashMap<String> relations = GraphAlgorithms.countRelations(graph);
			graphGroups.add(relations, graph);
		}

		// print groups
//		for (Object2IntOpenHashMap<String> group : graphGroups.keySet()) {
//			List<StringGraph> list = graphGroups.get(group);
//			System.out.println(list.size() + "\t" + group);
//		}
//
//		System.exit(0);

		// check for isomorphisms within groups
		HashSet<StringGraph> duplicatedGraphs = new HashSet<StringGraph>();
		Set<Object2IntOpenHashMap<String>> keySet = graphGroups.keySet();
		for (Object2IntOpenHashMap<String> key : keySet) {
			List<StringGraph> localGroup = graphGroups.get(key);
			// System.out.printf("%s\t%d\n", key, localGroup.size());
			duplicatedGraphs.addAll(findIsomorphisms(localGroup));
		}

		System.out.printf("got %d duplicated graphs \n", duplicatedGraphs.size());

		ArrayList<SemanticFrame> uniqueFrames = new ArrayList<SemanticFrame>(frames.size());
		for (SemanticFrame frame : frames) {
			StringGraph graph = frame.getGraph();
			if (duplicatedGraphs.contains(graph))
				continue;
			uniqueFrames.add(frame);
		}

		System.out.printf("%d unique frames \n", uniqueFrames.size());
	//	FrameReadWrite.writePatternFramesCSV(uniqueFrames, "../PatternMiner/results/resultsV22.csv");
		System.lineSeparator();
	}

	/**
	 * finds isomorphic graphs inside structural groups (based on their relations' histograms)
	 * 
	 * @param graphs
	 * @return
	 */
	private static Set<StringGraph> findIsomorphisms(List<StringGraph> graphs) {
		// repeated (isomorphic to some) graphs
		Set<StringGraph> repeatedGraphs = Collections.newSetFromMap(new ConcurrentHashMap<StringGraph, Boolean>());
		if (graphs.size() > 1) {
			// parallelize bigger (outer) for
			IntStream.range(0, graphs.size() - 1).parallel().forEach(i -> {
				StringGraph graph0 = graphs.get(i);
				if (!repeatedGraphs.contains(graph0)) {
					KnowledgeBase kb = buildKnowledgeBase(graph0);
					for (int j = i + 1; j < graphs.size(); j++) {
						// find graph1 in graph0
						StringGraph graph1 = graphs.get(j);
						if (!repeatedGraphs.contains(graph1)) {
							if (isGraphIsomorphicToKnowledgeBase(kb, graph1)) {
								repeatedGraphs.add(graph1);
							}
						}
					} // inner j for - variant graph1
				}
			});// i parallel for - variant knowledge base (graph0)
		}
		return repeatedGraphs;
	}

	private static boolean isGraphIsomorphicToKnowledgeBase(KnowledgeBase kb, StringGraph graph1) {
		HashMap<String, String> conceptToVariable = createConceptToVariableMapping(graph1);
		ArrayList<Conjunct> conjunctList = createConjunctionFromStringGraph(graph1, conceptToVariable);
		Query q = Query.make(conjunctList);
		int blockSize = 256;
		int parallelLimit = 1;
		BigInteger matches = kb.count(q, blockSize, parallelLimit, BigInteger.ONE, true, null);
		// graph1 contained in graph0
		boolean isIsomorphic = matches.compareTo(BigInteger.ZERO) > 0;
		return isIsomorphic;
	}
}
