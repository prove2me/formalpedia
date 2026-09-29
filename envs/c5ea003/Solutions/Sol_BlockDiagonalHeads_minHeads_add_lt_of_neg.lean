-- Prove2me | solution 1 for BlockDiagonalHeads.minHeads_add_lt_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:11:45.963984+00:00
-- url     : https://prove2.me/submissions/1e7ac54b-1551-4ae2-b2bf-d282dfb749aa

-- Sol generated from MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_BlockDiagonalHeads
import Theorems.Thm_BlockDiagonalHeads_Representable_finrank_le
import Theorems.Thm_BlockDiagonalHeads_representable_rankOf

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







/-- **Exact head complexity**: minimal head count = rank of the value table. -/
theorem minHeads_eq_rankOf [Finite X] (f : X → Y → ℝ) : minHeads f = rankOf f := by
  have hmem : rankOf f ∈ {H | Representable f H} := representable_rankOf f
  refine le_antisymm (Nat.sInf_le hmem) ?_
  exact (Nat.sInf_mem (⟨rankOf f, hmem⟩ : {H | Representable f H}.Nonempty) :
    Representable f (minHeads f)).finrank_le

/-! ## Coordinate inclusions of the two feature blocks -/






/-! ## The block-diagonal task -/








/-! ## Without the block structure, subadditivity is strict -/



open BlockDiagonalHeads in
theorem solution[Finite X] (f : X → Y → ℝ) (hf : f ≠ 0) :
    minHeads (fun x => f x + (-f) x) < minHeads f + minHeads (-f) := by
  have hzero : minHeads (fun x => f x + (-f) x) = 0 := by
    have : Representable (fun x => f x + (-f) x) 0 :=
      ⟨fun h => Fin.elim0 h, fun h => Fin.elim0 h, fun x => by simp⟩
    exact Nat.le_zero.mp (Nat.sInf_le this)
  have hpos : 0 < minHeads f := by
    rw [minHeads_eq_rankOf]
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
    have hmem : f x ∈ span ℝ (Set.range f) := Submodule.subset_span ⟨x, rfl⟩
    have hne : (span ℝ (Set.range f) : Submodule ℝ (Y → ℝ)) ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.mem_bot] at hmem
      exact hx (by simpa using hmem)
    have hnt : Nontrivial (span ℝ (Set.range f)) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    exact Module.finrank_pos
  omega
