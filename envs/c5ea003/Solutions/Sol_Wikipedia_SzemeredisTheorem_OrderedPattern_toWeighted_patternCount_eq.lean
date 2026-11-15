-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.OrderedPattern.toWeighted_patternCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:02:32.580424+00:00
-- url     : https://prove2.me/submissions/c326336f-f2c9-43ec-9afb-33f8c4690ea9

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

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









/-- An occurrence has zero-one pattern weight one. -/
theorem toWeighted_patternWeight_of_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 1 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  apply Finset.prod_eq_one
  intro e _he
  simp [toWeighted, hx e]

/-- A nonoccurrence has zero-one pattern weight zero. -/
theorem toWeighted_patternWeight_of_not_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 0 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  obtain ⟨e, he⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [toWeighted, he]













end OrderedPattern







end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.OrderedPattern

open Wikipedia.SzemeredisTheorem.OrderedPattern in
/-- The weighted normalized count is exactly the normalized cardinality of
the occurrence finset. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r) :
    H.toWeighted.patternCount =
      (H.occurrenceFinset.card : ℝ) /
        Fintype.card (Fin k → G) := by
  rw [WeightedOrderedPattern.patternCount]
  have hfun :
      H.toWeighted.patternWeight =
        finsetIndicator H.occurrenceFinset := by
    funext x
    by_cases hx : H.IsOccurrence x
    · rw [H.toWeighted_patternWeight_of_occurrence hx,
        finsetIndicator_of_mem]
      exact (H.mem_occurrenceFinset x).2 hx
    · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
        finsetIndicator_of_not_mem]
      exact fun hmem =>
        hx ((H.mem_occurrenceFinset x).1 hmem)
  rw [hfun, mean_finsetIndicator]
