-- Prove2me | solution 1 for HeadComplexity.Representable.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:08:55.03483+00:00
-- url     : https://prove2.me/submissions/363a8b34-9a5f-4b65-95b4-486f6d940ecb

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
omit [Fintype X] in
theorem solution{f : X → Y → ℝ} {H : ℕ} (hf : Representable f H) :
    rankOf f ≤ H := by
  classical
  obtain ⟨c, v, hcv⟩ := hf
  have hsub : span ℝ (Set.range f) ≤ span ℝ (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hcv x]
    exact Submodule.sum_mem _ fun h _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
  have hfin : Module.Finite ℝ (span ℝ (Set.range v)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range v)
  have hmono : finrank ℝ (span ℝ (Set.range f)) ≤ finrank ℝ (span ℝ (Set.range v)) :=
    Submodule.finrank_mono hsub
  have hcard : finrank ℝ (span ℝ (Set.range v)) ≤ H := by
    have h1 := finrank_span_le_card (R := ℝ) (Set.range v)
    have h2 : (Set.range v).toFinset.card ≤ H := by
      rw [Set.toFinset_range]
      exact le_trans Finset.card_image_le (by simp)
    exact le_trans h1 h2
  exact le_trans hmono hcard
