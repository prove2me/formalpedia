-- Prove2me | solution 1 for BlockDiagonalHeads.rankOf_blockTask
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:11:46.63598+00:00
-- url     : https://prove2.me/submissions/c7d3b004-7d89-437b-98a2-2274b5cf5146

-- Sol generated from MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_BlockDiagonalHeads
import Theorems.Thm_BlockDiagonalHeads_disjoint_incl_ranges

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



theorem inclL_injective : Function.Injective (inclL Y Y') := by
  intro u v huv
  funext y
  have := congrFun huv (Sum.inl y)
  simpa [inclL] using this

theorem inclR_injective : Function.Injective (inclR Y Y') := by
  intro u v huv
  funext y
  have := congrFun huv (Sum.inr y)
  simpa [inclR] using this


/-! ## The block-diagonal task -/


theorem range_blockTask (f : X → Y → ℝ) (g : X' → Y' → ℝ) :
    Set.range (blockTask f g) =
      (inclL Y Y' '' Set.range f) ∪ (inclR Y Y' '' Set.range g) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    cases w with
    | inl x => exact Or.inl ⟨f x, ⟨x, rfl⟩, rfl⟩
    | inr x' => exact Or.inr ⟨g x', ⟨x', rfl⟩, rfl⟩
  · rintro (⟨_, ⟨x, rfl⟩, rfl⟩ | ⟨_, ⟨x', rfl⟩, rfl⟩)
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr x', rfl⟩

/-- The output span of the block-diagonal task is the sum of the two pushed-forward spans. -/
theorem span_range_blockTask (f : X → Y → ℝ) (g : X' → Y' → ℝ) :
    span ℝ (Set.range (blockTask f g)) =
      Submodule.map (inclL Y Y') (span ℝ (Set.range f)) ⊔
        Submodule.map (inclR Y Y') (span ℝ (Set.range g)) := by
  rw [range_blockTask, Submodule.span_union, Submodule.span_image, Submodule.span_image]

/-- Pushing a span forward along an injective linear map preserves its dimension. -/
theorem finrank_map_incl_left [Finite X] (f : X → Y → ℝ) :
    finrank ℝ (Submodule.map (inclL Y Y') (span ℝ (Set.range f))) = rankOf f :=
  ((Submodule.equivMapOfInjective (inclL Y Y') inclL_injective
    (span ℝ (Set.range f))).finrank_eq).symm

theorem finrank_map_incl_right [Finite X'] (g : X' → Y' → ℝ) :
    finrank ℝ (Submodule.map (inclR Y Y') (span ℝ (Set.range g))) = rankOf g :=
  ((Submodule.equivMapOfInjective (inclR Y Y') inclR_injective
    (span ℝ (Set.range g))).finrank_eq).symm



/-! ## Without the block structure, subadditivity is strict -/



open BlockDiagonalHeads in
theorem solution[Finite X] [Finite X'] (f : X → Y → ℝ) (g : X' → Y' → ℝ) :
    rankOf (blockTask f g) = rankOf f + rankOf g := by
  classical
  set A := Submodule.map (inclL Y Y') (span ℝ (Set.range f)) with hA
  set B := Submodule.map (inclR Y Y') (span ℝ (Set.range g)) with hB
  have hAeq : A = span ℝ (Set.range fun x => inclL Y Y' (f x)) := by
    rw [hA, ← Submodule.span_image, ← Set.range_comp]; rfl
  have hBeq : B = span ℝ (Set.range fun x' => inclR Y Y' (g x')) := by
    rw [hB, ← Submodule.span_image, ← Set.range_comp]; rfl
  haveI : Module.Finite ℝ A := by
    rw [hAeq]; exact Module.Finite.span_of_finite ℝ (Set.finite_range _)
  haveI : Module.Finite ℝ B := by
    rw [hBeq]; exact Module.Finite.span_of_finite ℝ (Set.finite_range _)
  have hinf : A ⊓ B = ⊥ := disjoint_incl_ranges _ _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hinf] at hsum
  simp only [finrank_bot, add_zero] at hsum
  have hspan : span ℝ (Set.range (blockTask f g)) = A ⊔ B := span_range_blockTask f g
  rw [rankOf, hspan, hsum, hA, hB, finrank_map_incl_left, finrank_map_incl_right]
