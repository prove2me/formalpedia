-- Prove2me | Theorems.Thm_GoldbachReps_card_filter_even_range
-- name    : GoldbachReps.card_filter_even_range
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:27:27.660838+00:00
-- url     : https://prove2.me/theorems/ffc3b07b-a928-45e0-9f69-98ddb5dc2bff
-- title:
--   Card filter even range
-- statement:
--   Formal statement of `GoldbachReps.card_filter_even_range` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GoldbachReps.card_filter_even_range(M : ℕ) :
--       (Finset.filter (fun p => Even p) (Finset.range (M + 1))).card = M / 2 + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/NumberTheory/GoldbachReps.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/NumberTheory/GoldbachReps.lean#L41

-- Thm stub generated from Shared/NumberTheory/GoldbachReps.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_GoldbachReps

/-!
# Combinatorial properties of the Goldbach representation counter

This file defines a representation counter `reps A n`, counting the number of
*unordered* representations `n = p + q` with `p, q ∈ A` (encoded by `p ≤ n - p`),
and proves several structural results about it.

The headline result is `reps_symmetric_eq`: if a set `A` is symmetric about `n/2`
(closed under `k ↦ n - k` on its elements `≤ n`), then `reps A n` simply counts the
elements of `A` in the lower half `{0, …, ⌊n/2⌋}`.  From it we derive the value for the
full set, an upper bound valid for every set, and the exact value for the set of even
numbers.

All core arguments are explicit Finset manipulations (`Finset.ext`, `Finset.card_nbij'`,
`Finset.card_le_card`, `Finset.filter_eq_empty_iff`), with arithmetic discharged by
`omega`; no `aesop`/`grind` is used.
-/

open GoldbachReps

open Classical

theorem GoldbachReps.card_filter_even_range(M : ℕ) :
    (Finset.filter (fun p => Even p) (Finset.range (M + 1))).card = M / 2 + 1 := by sorry
