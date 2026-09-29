-- Prove2me | solution 1 for HeadComplexity.representable_finrank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:08:55.995673+00:00
-- url     : https://prove2.me/submissions/880b86c9-f390-4126-9b2f-617ae65cae31

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
theorem solution(f : X → Y → ℝ) : Representable f (rankOf f) := by
  classical
  set W : Submodule ℝ (Y → ℝ) := span ℝ (Set.range f) with hW
  set b : Basis (Fin (finrank ℝ W)) ℝ W := Module.finBasis ℝ W with hb
  set v : Fin (rankOf f) → (Y → ℝ) := fun i => (b i : Y → ℝ) with hv
  have hspan : span ℝ (Set.range v) = W := by
    have h : Set.range v = W.subtype '' (Set.range b) := by
      rw [← Set.range_comp]; rfl
    rw [hv] at h ⊢
    rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hmem : ∀ x, ∃ c : Fin (rankOf f) → ℝ, ∑ i, c i • v i = f x := by
    intro x
    have hx : f x ∈ span ℝ (Set.range v) := by
      rw [hspan, hW]
      exact Submodule.subset_span ⟨x, rfl⟩
    exact (mem_span_range_iff_exists_fun ℝ).mp hx
  choose c hc using hmem
  exact ⟨fun i x => c x i, v, fun x => (hc x).symm⟩
