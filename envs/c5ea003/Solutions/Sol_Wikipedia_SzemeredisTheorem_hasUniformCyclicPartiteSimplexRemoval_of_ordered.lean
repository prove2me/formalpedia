-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasUniformCyclicPartiteSimplexRemoval_of_ordered
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:53:29.371315+00:00
-- url     : https://prove2.me/submissions/33f4bdb5-8882-49c7-9e4c-b37fff8c71bc

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_OrderedPattern_toWeighted_patternCount_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SimplexHypergraph_isSimplexCover_orderedDeletionToSimplex
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SimplexHypergraph_toOrderedPattern_isOccurrence_iff
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SimplexHypergraph_toWeighted_simplexWeight_eq_indicator
import Theorems.Thm_Wikipedia_SzemeredisTheorem_normalizedDeletionCost_orderedDeletionToSimplex_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

























end Wikipedia.SzemeredisTheorem

end

section


/-!
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































namespace WeightedOrderedPattern











end WeightedOrderedPattern



namespace OrderedPattern





@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]

























end OrderedPattern







end Wikipedia.SzemeredisTheorem

end

section


/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



namespace SimplexHypergraph





















/-- The normalized weighted count is the number of labelled simplices divided
by the size of the ambient product. -/
theorem toWeighted_simplexCount_eq_card_div {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.toWeighted.simplexCount =
      (H.simplexFinset.card : ℝ) /
        Fintype.card ((i : Fin k) → V i) := by
  classical
  rw [WeightedSimplexSystem.simplexCount]
  have hfun :
      H.toWeighted.simplexWeight =
        finsetIndicator H.simplexFinset := by
    funext x
    exact toWeighted_simplexWeight_eq_indicator H x
  rw [hfun, mean_finsetIndicator]





end SimplexHypergraph

end Wikipedia.SzemeredisTheorem

end

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















end Wikipedia.SzemeredisTheorem

end

section




/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators























/-- The finite occurrence set is unchanged by the ordered presentation. -/
theorem SimplexHypergraph.toOrderedPattern_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.occurrenceFinset =
      H.simplexFinset := by
  ext x
  rw [OrderedPattern.mem_occurrenceFinset,
    SimplexHypergraph.mem_simplexFinset,
    H.toOrderedPattern_isOccurrence_iff]

/-- In particular, the zero-one normalized pattern count is exactly the
zero-one normalized simplex count. -/
theorem SimplexHypergraph.toOrderedPattern_patternCount
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.toWeighted.patternCount =
      H.toWeighted.simplexCount := by
  classical
  rw [OrderedPattern.toWeighted_patternCount_eq,
    SimplexHypergraph.toWeighted_simplexCount_eq_card_div,
    H.toOrderedPattern_occurrenceFinset]

















end Wikipedia.SzemeredisTheorem

end
/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Uniform ordered removal for rank `n` patterns on `n + 1` equal vertex
classes implies uniform cyclic partite simplex removal on `n + 1` colours. -/
theorem solution
    (n : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (n + 1) n) :
    HasUniformCyclicPartiteSimplexRemoval (n + 1) := by
  intro ε hε
  obtain ⟨c, hc, hremove⟩ := hordered ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst H hcount
  have horderedCount :
      H.toOrderedPattern.toWeighted.patternCount < c := by
    rw [H.toOrderedPattern_patternCount]
    exact hcount
  obtain ⟨D, hcover, hD⟩ :=
    hremove (ZMod N) H.toOrderedPattern horderedCount
  exact
    ⟨orderedDeletionToSimplex D,
      H.isSimplexCover_orderedDeletionToSimplex D hcover,
      normalizedDeletionCost_orderedDeletionToSimplex_le D hD⟩
