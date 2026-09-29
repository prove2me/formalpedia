-- Prove2me | Theorems.Thm_BlockDiagonalHeads_minHeads_add_lt_of_neg
-- name    : BlockDiagonalHeads.minHeads_add_lt_of_neg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:25:37.76133+00:00
-- url     : https://prove2.me/theorems/cfb9a8f0-0785-46f2-b1d4-648899383d34
-- title:
--   Strictness of plain subadditivity.
-- statement:
--   **Strictness of plain subadditivity.**  For a nonzero task `f`, the pair `(f, -f)` has
--   `minHeads f + minHeads (-f) = 2 · minHeads f > 0 = minHeads (f + (-f))`, so the block structure
--   in `minHeads_blockTask` is essential.
--
--   ```lean
--   theorem BlockDiagonalHeads.minHeads_add_lt_of_neg[Finite X] (f : X → Y → ℝ) (hf : f ≠ 0) :
--       minHeads (fun x => f x + (-f) x) < minHeads f + minHeads (-f) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean#L219

-- Thm stub generated from MachineLearning/TransformerUniversality/BlockDiagonalHeads.lean
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

theorem BlockDiagonalHeads.minHeads_add_lt_of_neg[Finite X] (f : X → Y → ℝ) (hf : f ≠ 0) :
    minHeads (fun x => f x + (-f) x) < minHeads f + minHeads (-f) := by sorry
