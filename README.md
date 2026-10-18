# Chordal, split, threshold and cograph structure in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Classical structural results on chordal graphs and the related classes of split, threshold and
cographs, for finite simple graphs. All statements are in the namespace `ChordalClasses`.

**Chordal graphs.** A graph is *chordal* if every cycle of length at least four has a chord.

1. `minimalSeparator_isClique`, **Dirac (1961)**: every minimal `a`–`b` separator of a chordal
   graph is a clique.
2. `exists_isSimplicial` and `exists_two_nonadj_isSimplicial`, **Dirac (1961)**: a nonempty finite
   chordal graph has a simplicial vertex (one whose neighbourhood is a clique); if it is connected
   and not complete, it has two non-adjacent simplicial vertices.
3. `isChordal_iff_exists_isPEO`, **Fulkerson–Gross (1965)**: a finite graph is chordal if and
   only if it has a perfect elimination order.
4. `isChordal_iff_nonempty_subtreeRepresentation`, **Gavril (1974)**: a finite graph is chordal if
   and only if it is the intersection graph of subtrees of a finite tree.
5. `treewidth_succ_eq_cliqueNum`: a nonempty finite chordal graph has treewidth `ω(G) − 1`, and
   `cliqueNum_le_treewidth_succ`: every finite graph has `ω(G) ≤ tw(G) + 1`.

**Split, threshold and cographs.** A graph is *split* if its vertices can be partitioned into a
clique and an independent set; *threshold* if, moreover, the neighbourhoods of the independent
vertices are nested; a *cograph* if it has no induced path on four vertices.

6. `isSplit_iff_isChordal_and_compl` and `isSplit_iff_forbidden_induced_subgraphs`,
   **Földes–Hammer (1977)**: a finite graph is split if and only if it and its complement are
   chordal, if and only if it has no induced `2K₂`, `C₄` or `C₅`.
7. `isThreshold_iff_forbidden_induced_subgraphs`, **Chvátal–Hammer (1977)**: a finite graph is
   threshold if and only if it has no induced `2K₂`, `C₄` or `P₄`; and
   `isThreshold_iff_isSplit_and_isCograph`: threshold graphs are exactly the split cographs.
8. `isCograph_iff_not_pathGraph_four_isIndContained`: the cograph condition agrees with Mathlib's
   induced containment of `pathGraph 4`.

Mathlib has none of these classes. The definitions (`SimpleGraph.IsChordal`, `SimpleGraph.IsPEO`,
`SimpleGraph.SubtreeRepresentation`, `SimpleGraph.IsSplit`, `SimpleGraph.IsThreshold`,
`SimpleGraph.IsCograph`, `Utilities.Treewidth.treewidth`, ...) are stated at the top of
`Challenge.lean`, verbatim and with the same names as in the library; the comparator checks every
definition used by a statement, declaration by declaration, against the library's.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean): each theorem is the corresponding library theorem.
- [`GraphClassesLib/`](GraphClassesLib): the library, merged upstream in
  [Lean Pool](https://github.com/LeanPool/lean-pool) (PRs
  [#349](https://github.com/LeanPool/lean-pool/pull/349),
  [#577](https://github.com/LeanPool/lean-pool/pull/577),
  [#583](https://github.com/LeanPool/lean-pool/pull/583) and
  [#587](https://github.com/LeanPool/lean-pool/pull/587)), copied from Lean Pool commit `49cfa8b`
  with the module prefix `LeanPool.` renamed to `GraphClassesLib.` and, in `Chordal.lean` and
  `Split.lean`, the selective Mathlib imports replaced by `import Mathlib` (so that the
  definitions elaborate with the same instances as in `Challenge.lean`):
  - `Erdos81PaperIIContrib/Chordal.lean`: chordal graphs, minimal separators, Dirac's theorems;
  - `PaperIVCliqueTree/`: perfect elimination orders, clique trees, Helly property, Gavril's
    theorem, exact treewidth of chordal graphs;
  - `StructuralGraphClasses/`: split partitions, cotrees, threshold creation sequences and the
    forbidden-subgraph characterizations;
  - `BrillNoetherGraphs/TreewidthGonality/Treewidth/TreeDecomposition.lean`: tree decompositions
    and treewidth, **by Nathan Pflueger** (Lean Pool, Apache-2.0), included unchanged except for
    the module prefix.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

The library also proves results that are not part of the audited statements: the clique-tree
characterization of chordal graphs, cotree representations of cographs, threshold creation
sequences, and counting and gluing lemmas for clique trees.

## How the proofs go

* **Dirac.** If a minimal `a`–`b` separator contained two non-adjacent vertices `x` and `y`, the
  components of `a` and `b` would give two internally disjoint induced `x`–`y` paths, which
  together form a chordless cycle of length at least four. A simplicial vertex is found by strong
  induction on the number of vertices; in the connected non-complete case, using a minimal
  separator `S` and a component of `G − S`.
* **Fulkerson–Gross.** Removing simplicial vertices one at a time gives a perfect elimination
  order. Conversely, a perfect elimination order builds a clique tree, and graphs with a clique
  tree are chordal.
* **Gavril.** A chordal graph has a clique forest, which gives a subtree representation.
  Conversely, pruning a leaf of the host tree shows that a graph with a subtree representation has
  a perfect elimination order.
* **Treewidth.** The clique tree of a chordal graph is a tree decomposition whose bags are cliques;
  by the Helly property of the bags, the clique number is the size of the largest bag. In every
  tree decomposition each clique lies in a single bag, so `ω ≤ tw + 1`.
* **Split and threshold.** A split partition of `G` minus a simplicial vertex extends to `G` when
  there is no induced `2K₂`, so chordal graphs without induced `2K₂` are split; chordless cycles of
  length at least six contain an induced `2K₂`. Within a split partition, nested neighbourhoods of
  the independent vertices are equivalent to excluding an induced `P₄`.

## Sources

* G. A. Dirac, *On rigid circuit graphs*, Abh. Math. Sem. Univ. Hamburg 25 (1961) 71–76,
  doi:10.1007/BF02992776.
* D. R. Fulkerson, O. A. Gross, *Incidence matrices and interval graphs*, Pacific J. Math. 15
  (1965) 835–855, doi:10.2140/pjm.1965.15.835.
* F. Gavril, *The intersection graphs of subtrees in trees are exactly the chordal graphs*,
  J. Combin. Theory Ser. B 16 (1974) 47–56, doi:10.1016/0095-8956(74)90094-X.
* S. Földes, P. L. Hammer, *Split graphs*, Proc. 8th Southeastern Conference on Combinatorics,
  Graph Theory and Computing (1977), Congressus Numerantium XIX, 311–315.
* V. Chvátal, P. L. Hammer, *Aggregation of inequalities in integer programming*, Annals of
  Discrete Mathematics 1 (1977) 145–162, doi:10.1016/S0167-5060(08)70731-3.
* R. Diestel, *Graph Theory*, Graduate Texts in Mathematics 173, 5th ed., Springer (2017),
  doi:10.1007/978-3-662-53622-3, Chapter 12 (tree-decompositions and chordal graphs).

## Authorship and use of AI

The author chose the results and directed the work. The library was written with AI assistance
(Claude, in Claude Code) and reviewed and merged in Lean Pool; the file
`TreeDecomposition.lean` is by Nathan Pflueger. Lean checks everything mechanically. See
`formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
