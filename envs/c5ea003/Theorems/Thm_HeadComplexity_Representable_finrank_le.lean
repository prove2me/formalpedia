-- Prove2me | Theorems.Thm_HeadComplexity_Representable_finrank_le
-- name    : HeadComplexity.Representable.finrank_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:36:38.281677+00:00
-- url     : https://prove2.me/theorems/f9815bba-1911-4002-bdb2-61eb17b332c2
-- title:
--   Head lower bound.
-- statement:
--   **Head lower bound.**  Any `H`-head value-sum model of `f` has all its outputs inside an
--   `H`-dimensional subspace, so the rank of the value table is at most `H`.
--
--   ```lean
--   theorem HeadComplexity.Representable.finrank_le{f : X → Y → ℝ} {H : ℕ} (hf : Representable f H) :
--       rankOf f ≤ H := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/HeadComplexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/HeadComplexity.lean#L50

-- Thm stub generated from MachineLearning/TransformerUniversality/HeadComplexity.lean
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




omit [Fintype X] in

theorem HeadComplexity.Representable.finrank_le{f : X → Y → ℝ} {H : ℕ} (hf : Representable f H) :
    rankOf f ≤ H := by sorry
