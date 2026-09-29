-- Prove2me | solution 1 for HeadComplexity.minHeads_le_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:08:55.487154+00:00
-- url     : https://prove2.me/submissions/26e48c39-b3c8-4edf-9082-0db42900eb4c

-- Sol generated from MachineLearning/TransformerUniversality/HeadComplexity.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_HeadComplexity

/-!
# Exact head complexity of the attention lookup architecture

The catalog file `Catalog/MachineLearning/TransformerArchitecture.lean` realizes an arbitrary
function on a finite domain using **one head per possible input**, and explicitly flags the
resulting head count as a defect.  This file settles the question exactly.

A *value-sum architecture with `H` heads* computes
`model x = ∑ h : Fin H, c h x • v h`,
where the scalar gates `c h : X → ℝ` may be arbitrary (this is more general than attention:
softmax gates, bilinear gates, or any nonlinear gate are all special cases) and the `H` value
vectors `v h` are input-independent.  The catalog architecture is the special case
`c a x = ⟦x = a⟧`, `v a = f a`, with `H = |X|`.

Main results:

* `Representable.finrank_le` — a lower bound: any `H`-head model of `f` forces
  `finrank (span (range f)) ≤ H`;
* `representable_finrank` — a matching constructive upper bound: `finrank (span (range f))`
  heads always suffice;
* `minHeads_eq_finrank` — hence the minimal head count is *exactly* the rank of the value
  table, an exact resource characterization;
* `minHeads_eq_card_of_linearIndependent` — the catalog's `|X|` heads are necessary precisely
  when the value tables are linearly independent, and
* `minHeads_le_one_of_rank_one` — a family of tasks where a single head replaces `|X|` of
  them, so the exponential head count of exact finite lookup is an artifact of worst-case
  rank, not of the architecture.
-/

open scoped BigOperators
open Submodule Set Module

open HeadComplexity

variable {X Y : Type*} [Fintype X]













open HeadComplexity in
theorem solution[DecidableEq X] (f : X → Y → ℝ) :
    minHeads f ≤ Fintype.card X := by
  classical
  have hrep : Representable f (Fintype.card X) := by
    obtain ⟨e⟩ : Nonempty (Fin (Fintype.card X) ≃ X) := ⟨(Fintype.equivFin X).symm⟩
    refine ⟨fun h x => if x = e h then 1 else 0, fun h => f (e h), fun x => ?_⟩
    rw [Finset.sum_eq_single (e.symm x)]
    · simp
    · intro h _ hne
      have : x ≠ e h := by
        intro hx
        exact hne (by rw [hx, Equiv.symm_apply_apply])
      simp [this]
    · intro hx
      exact absurd (Finset.mem_univ _) hx
  exact Nat.sInf_le hrep
