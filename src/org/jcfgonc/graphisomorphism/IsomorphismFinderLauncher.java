package org.jcfgonc.graphisomorphism;

import java.io.IOException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import com.githhub.aaronbembenek.querykb.Conjunct;
import com.githhub.aaronbembenek.querykb.KnowledgeBase;
import com.githhub.aaronbembenek.querykb.KnowledgeBaseBuilder;

import frames.FrameReadWrite;
import frames.SemanticFrame;
import graph.GraphAlgorithms;
import graph.StringEdge;
import graph.StringGraph;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import structures.MapOfList;
import utils.JatalogInterface;
import utils.VariousUtils;
import za.co.wstoop.jatalog.DatalogException;
import za.co.wstoop.jatalog.Expr;

public class IsomorphismFinderLauncher {
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

	public static void main(String[] args) {
		// read graphs
		String framesFilename = "../PatternMiner/results/resultsV22.csv";
		ArrayList<SemanticFrame> frames = null;
		try {
			frames = FrameReadWrite.readPatternFrames(framesFilename);
		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		int numFrames = frames.size();

		// map histograms to list of graph's indices
		MapOfList<Object2IntOpenHashMap<String>, Integer> graphGroups = new MapOfList<Object2IntOpenHashMap<String>, Integer>();
		ArrayList<StringGraph> graphs = new ArrayList<StringGraph>(numFrames);
		// organize graphs in groups according to the relations' histograms
		// store graphs in the arraylist
		for (int i = 0; i < numFrames; i++) {
			SemanticFrame frame = frames.get(i);
			StringGraph graph = frame.getFrame();
			Object2IntOpenHashMap<String> relations = GraphAlgorithms.countRelations(graph);
			graphGroups.add(relations, i);
			graphs.add(graph);
		}

		// print groups
//		Iterator<Entry<Object2IntOpenHashMap<String>, List<Integer>>> iterator = graphGroups.entrySet().iterator();
//		while (iterator.hasNext()) {
//			Entry<Object2IntOpenHashMap<String>, List<Integer>> next = iterator.next();
//			System.out.printf("%s\t%s\n", next.getKey(), next.getValue().size());
//		}

		// check for isomorphisms within groups
		BitSet isomorphicGraphs = new BitSet(frames.size());// list of repeated (isomorphic to some) graphs
		try {
			Set<Object2IntOpenHashMap<String>> keySet = graphGroups.keySet();
			for (Object2IntOpenHashMap<String> key : keySet) {
				List<Integer> localGroup = graphGroups.get(key);
				findIsomorphismsInGroup(graphs, localGroup, isomorphicGraphs);
			}
		} catch (DatalogException e) {
			e.printStackTrace();
			System.exit(-2);
		}

		System.out.printf("found %d duplicated graphs \n", isomorphicGraphs.cardinality());

		ArrayList<SemanticFrame> uniqueFrames = new ArrayList<SemanticFrame>(numFrames);
		for (int i = 0; i < numFrames; i++) {
			SemanticFrame frame = frames.get(i);
			if (isomorphicGraphs.get(i))
				continue;
			uniqueFrames.add(frame);
		}
		System.out.printf("%d unique frames \n", uniqueFrames.size());

		try {
			String outFilename = VariousUtils.appendSuffixToFilename(framesFilename, "_noiso");
			FrameReadWrite.writePatternFramesCSV(uniqueFrames, outFilename);
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.lineSeparator();
	}

	/**
	 * finds isomorphic graphs inside structural groups (based on their relations' histograms)
	 * 
	 * @param graphs
	 * @return
	 * @throws DatalogException
	 */
	private static void findIsomorphismsInGroup(ArrayList<StringGraph> graphs, List<Integer> localGroup, BitSet isomorphicGraphs)
			throws DatalogException {
		if (localGroup.size() > 1) {
			// one jatalog for each thread
			JatalogInterface jatai = new JatalogInterface();
			// generate combinations of two elements
			for (int i = 0; i < localGroup.size() - 1; i++) {

				int index_i = localGroup.get(i).intValue();
				StringGraph graph_i = graphs.get(index_i);
				boolean duplicated_i = isomorphicGraphs.get(index_i);
				if (!duplicated_i) {

					StringGraph graphGrounded = GraphAlgorithms.convertGraphToConstantGraph(graph_i);
					jatai.addFacts(graphGrounded);

					for (int j = i + 1; j < localGroup.size(); j++) {
						// find graph1 in graph0
						int index_j = localGroup.get(j).intValue();
						StringGraph graph_j = graphs.get(index_j);
						boolean duplicated_j = isomorphicGraphs.get(index_j);
						if (!duplicated_j) {
							StringGraph graphGeneralized = GraphAlgorithms.convertGraphToVariableGraph(graph_j);
							ArrayList<Expr> query = jatai.createQueryFromStringGraphUniqueInstantiation(graphGeneralized);
							boolean isIsomorphic = isGraphIsomorphicToKnowledgeBase(jatai, query);
							if (isIsomorphic) {
								isomorphicGraphs.set(index_j);
							}
						}
					} // inner j for - variant graph1
					jatai.clear();
				}
			} // );// outer i for - variant knowledge base (graph0)
		}
	}

	private static boolean isGraphIsomorphicToKnowledgeBase(JatalogInterface ji, ArrayList<Expr> query) throws DatalogException {
		boolean isIsomorphic = ji.isQueryTrue(query);
		return isIsomorphic;
	}
}
