-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_BlockDiagonalHeads
-- name    : MachineLearning_TransformerUniversality_BlockDiagonalHeads
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:03.194677+00:00
-- url     : https://prove2.me/theorems/f9972a6b-d3ce-46f8-a59b-21e08e68a1a8
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_BlockDiagonalHeads
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.BlockDiagonalHeads`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean by skeleton subtraction
import Mathlib

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

namespace BlockDiagonalHeads

/-! ## The head-complexity measure (as in `HeadComplexity.lean`) -/

variable {X X' Y Y' : Type*}

/-- A value-sum architecture with `H` heads: input-dependent scalar gates times
input-independent value vectors. -/
def Representable (f : X → Y → ℝ) (H : ℕ) : Prop :=
  ∃ (c : Fin H → X → ℝ) (v : Fin H → (Y → ℝ)), ∀ x, f x = ∑ h, c h x • v h

/-- The rank of the value table. -/
noncomputable def rankOf (f : X → Y → ℝ) : ℕ := finrank ℝ (span ℝ (Set.range f))

/-- The minimal number of heads of a value-sum architecture computing `f`. -/
noncomputable def minHeads (f : X → Y → ℝ) : ℕ := sInf {H | Representable f H}

instance finiteSpanRange [Finite X] (f : X → Y → ℝ) : Module.Finite ℝ (span ℝ (Set.range f)) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range f)




/-! ## Coordinate inclusions of the two feature blocks -/

/-- The inclusion of the first feature block `Y ↪ Y ⊕ Y'`, as a linear map on functions. -/
def inclL (Y Y' : Type*) : (Y → ℝ) →ₗ[ℝ] (Y ⊕ Y' → ℝ) where
  toFun u := Sum.elim u 0
  map_add' u v := by funext z; cases z <;> simp
  map_smul' a u := by funext z; cases z <;> simp

/-- The inclusion of the second feature block `Y' ↪ Y ⊕ Y'`. -/
def inclR (Y Y' : Type*) : (Y' → ℝ) →ₗ[ℝ] (Y ⊕ Y' → ℝ) where
  toFun w := Sum.elim 0 w
  map_add' u v := by funext z; cases z <;> simp
  map_smul' a u := by funext z; cases z <;> simp




/-! ## The block-diagonal task -/

/-- The **block-diagonal combination** of two tasks: on inputs from `X` it computes `f` in the
first feature block and zero in the second, and symmetrically on inputs from `X'`. -/
def blockTask (f : X → Y → ℝ) (g : X' → Y' → ℝ) : (X ⊕ X') → (Y ⊕ Y' → ℝ) :=
  Sum.elim (fun x => inclL Y Y' (f x)) (fun x' => inclR Y Y' (g x'))







/-! ## Without the block structure, subadditivity is strict -/


end BlockDiagonalHeads


