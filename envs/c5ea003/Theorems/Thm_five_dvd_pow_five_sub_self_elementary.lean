-- Prove2me | Theorems.Thm_five_dvd_pow_five_sub_self_elementary
-- name    : five_dvd_pow_five_sub_self_elementary
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:25:52.475398+00:00
-- url     : https://prove2.me/theorems/d17a7b16-e015-4216-b475-4f8542667a2a
-- title:
--   The special case `5 ∣ a ^ 5 - a` via the factorisation
-- statement:
--   The special case `5 ∣ a ^ 5 - a` via the factorisation
--   `a ^ 5 - a = (a - 1) * a * (a + 1) * (a ^ 2 + 1)` and a case analysis on `a % 5`.
--
--   ```lean
--   theorem five_dvd_pow_five_sub_self_elementary(a : ℤ) : 5 ∣ a ^ 5 - a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FermatLittleFive.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FermatLittleFive.lean#L41

-- Thm stub generated from Probability/FermatLittleFive.lean
import Mathlib

/-!
# Fermat's Little Theorem and the divisibility `5 ∣ a ^ 5 - a`

This file records Fermat's little theorem over the integers together with several
proofs of the special case `5 ∣ a ^ 5 - a`.
-/

open scoped BigOperators

theorem five_dvd_pow_five_sub_self_elementary(a : ℤ) : 5 ∣ a ^ 5 - a := by sorry
