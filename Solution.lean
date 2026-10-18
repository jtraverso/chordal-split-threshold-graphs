/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import GraphClassesLib.PaperIVCliqueTree
public import GraphClassesLib.StructuralGraphClasses

/-!
# Proofs of the statements in `Challenge.lean`

The definitions used by the statements (`SimpleGraph.IsChordal`, `SimpleGraph.IsPEO`,
`SimpleGraph.SubtreeRepresentation`, `SimpleGraph.SplitPartition`, `SimpleGraph.IsSplit`,
`SimpleGraph.IsThreshold`, `SimpleGraph.IsCograph`, `Utilities.Treewidth.treewidth`, ...) are
the library's own declarations, imported from `GraphClassesLib/`; `Challenge.lean` reproduces them
verbatim. Each theorem is the corresponding library theorem:

* chordal graphs, Dirac's theorems: `GraphClassesLib/Erdos81PaperIIContrib/Chordal.lean`;
* perfect elimination orders, clique trees, Gavril's theorem and chordal treewidth:
  `GraphClassesLib/PaperIVCliqueTree/`;
* split, threshold and cograph characterizations: `GraphClassesLib/StructuralGraphClasses/`;
* tree decompositions and treewidth (by Nathan Pflueger, from Lean Pool):
  `GraphClassesLib/BrillNoetherGraphs/TreewidthGonality/Treewidth/TreeDecomposition.lean`.
-/

@[expose] public section

/-! ## Statements -/

namespace ChordalClasses

open SimpleGraph

section

variable {V : Type*} {G : SimpleGraph V}

/-- **Dirac (1961).** In a chordal graph, every finite minimal separator of two fixed vertices is a
clique. -/
theorem minimalSeparator_isClique (hG : G.IsChordal) {S : Finset V} {a b : V}
    (hS : G.IsMinimalSeparator (S : Set V) a b) : G.IsClique (S : Set V) :=
  hG.minimalSeparator_isClique hS

/-- **Dirac (1961).** A nonempty finite chordal graph has a simplicial vertex. -/
theorem exists_isSimplicial [Finite V] [Nonempty V] (hG : G.IsChordal) :
    ∃ v : V, G.IsSimplicial v :=
  hG.exists_isSimplicial

/-- **Dirac (1961).** A connected non-complete finite chordal graph has two distinct non-adjacent
simplicial vertices. -/
theorem exists_two_nonadj_isSimplicial [Finite V] (hG : G.IsChordal) (hconn : G.Connected)
    (hnc : ¬ ∀ u v : V, u ≠ v → G.Adj u v) :
    ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y ∧ G.IsSimplicial x ∧ G.IsSimplicial y :=
  hG.exists_two_nonadj_isSimplicial hconn hnc

/-- **Fulkerson–Gross (1965).** A finite graph is chordal if and only if it has a perfect
elimination order. -/
theorem isChordal_iff_exists_isPEO [Finite V] : G.IsChordal ↔ ∃ ord : V → ℕ, G.IsPEO ord :=
  SimpleGraph.isChordal_iff_exists_isPEO

/-- Every finite graph has clique number at most its treewidth plus one. -/
theorem cliqueNum_le_treewidth_succ [Finite V] (G : SimpleGraph V) :
    G.cliqueNum ≤ Utilities.Treewidth.treewidth G + 1 :=
  Utilities.Treewidth.cliqueNum_le_treewidth_succ G

/-- **Földes–Hammer (1977).** A finite graph is split if and only if it and its complement are
chordal. -/
theorem isSplit_iff_isChordal_and_compl [Finite V] : G.IsSplit ↔ G.IsChordal ∧ Gᶜ.IsChordal :=
  SimpleGraph.isSplit_iff_isChordal_and_compl

/-- **Földes–Hammer (1977).** A finite graph is split if and only if it has no induced `2K₂`, `C₄`
or `C₅`. -/
theorem isSplit_iff_forbidden_induced_subgraphs [Finite V] :
    G.IsSplit ↔
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) ∧
      (¬(cycleGraph 4).IsIndContained G) ∧ ¬(cycleGraph 5).IsIndContained G :=
  SimpleGraph.isSplit_iff_forbidden_induced_subgraphs

/-- Cographs (no induced four-vertex path) are exactly the graphs with no induced `P₄` in the
sense of Mathlib's induced containment. -/
theorem isCograph_iff_not_pathGraph_four_isIndContained :
    G.IsCograph ↔ ¬(pathGraph 4).IsIndContained G :=
  SimpleGraph.isCograph_iff_not_pathGraph_four_isIndContained

/-- Threshold graphs are exactly the split cographs. -/
theorem isThreshold_iff_isSplit_and_isCograph : G.IsThreshold ↔ G.IsSplit ∧ G.IsCograph :=
  SimpleGraph.isThreshold_iff_isSplit_and_isCograph

/-- **Chvátal–Hammer (1977).** A finite graph is threshold if and only if it has no induced `2K₂`,
`C₄` or `P₄`. -/
theorem isThreshold_iff_forbidden_induced_subgraphs [Finite V] :
    G.IsThreshold ↔
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) ∧
      (¬(cycleGraph 4).IsIndContained G) ∧ ¬(pathGraph 4).IsIndContained G :=
  SimpleGraph.isThreshold_iff_forbidden_induced_subgraphs

end

section

variable {V : Type} {G : SimpleGraph V}

/-- **Gavril (1974).** A finite graph is chordal if and only if it is the intersection graph of a
family of subtrees of a finite tree. -/
theorem isChordal_iff_nonempty_subtreeRepresentation [Finite V] :
    G.IsChordal ↔ Nonempty (SubtreeRepresentation G) :=
  SimpleGraph.isChordal_iff_nonempty_subtreeRepresentation

/-- A nonempty finite chordal graph has treewidth exactly its clique number minus one. -/
theorem treewidth_succ_eq_cliqueNum [Finite V] [Nonempty V] (hG : G.IsChordal) :
    Utilities.Treewidth.treewidth G + 1 = G.cliqueNum :=
  hG.treewidth_succ_eq_cliqueNum

end

end ChordalClasses
