-- Prove2me | solution 1 for BlockDiagonalHeads.representable_rankOf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:09:00.176237+00:00
-- url     : https://prove2.me/submissions/6668d69c-689b-4059-86dc-ba36926788cd

-- Sol generated from MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_BlockDiagonalHeads

/-!
# Head complexity of block-diagonal tasks: subadditivity is an equality

`Catalog/MachineLearning/TransformerUniversality/HeadComplexity.lean` shows that the minimal
number of heads of a value-sum architecture computing a finite value table equals the rank of
that table, and `HeadComposition.lean` shows that this resource is *subadditive*:
`minHeads (f + g) ≤ minHeads f + minHeads g`.  The second next-cycle sub-conjecture of
`FUTURE_DIRECTIONS.md` asked for the equality case.

Subadditivity is genuinely strict for a plain sum of tasks (take `g = -f`: the sum is the zero
task, which needs no heads at all).  The equality case is the *block-diagonal* task: run `f` on
one group of inputs and `g` on a disjoint group, writing their outputs into disjoint groups of
output features.  This file proves that heads then add exactly:

* `blockTask` — the block-diagonal combination of `f : X → Y → ℝ` and `g : X' → Y' → ℝ`, a task
  on `X ⊕ X'` with feature space `Y ⊕ Y'`;
* `span_range_blockTask` — its output span is the (internal direct) sum of the two output
  spans, pushed forward along the two coordinate inclusions;
* `rankOf_blockTask` — hence `rank (f ⊞ g) = rank f + rank g`;
* `minHeads_blockTask` — **no sharing is possible**: `minHeads (f ⊞ g) = minHeads f + minHeads g`,
  the equality case of `HeadComposition.minHeads_add_le`;
* `minHeads_add_lt_of_neg` — and the inequality really is strict without the block structure.

Interpretation: attention heads cannot be amortized across independent sub-tasks.  A
transformer that must solve `k` unrelated lookup problems in disjoint feature blocks needs the
sum of the individual head budgets — the parallelism of multi-head attention buys no
compression, only the freedom to allocate.  Since `minHeads` is also invariant under linear
isomorphisms (`HeadComposition.minHeads_postcomp_of_injective`), this pins down `minHeads` as
an additive invariant of the value table.

As every catalog file is self-contained, the definitions and the rank characterization of
`HeadComplexity.lean` are repeated here.
-/

open scoped BigOperators
open Submodule Set Module

open BlockDiagonalHeads

/-! ## The head-complexity measure (as in `HeadComplexity.lean`) -/

variable {X X' Y Y' : Type*}








/-! ## Coordinate inclusions of the two feature blocks -/






/-! ## The block-diagonal task -/








/-! ## Without the block structure, subadditivity is strict -/



open BlockDiagonalHeads in
theorem solution[Finite X] (f : X → Y → ℝ) : Representable f (rankOf f) := by
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
