-- Prove2me | Theorems.Thm_RecursiveMixedRadix_digit_decomposition
-- name    : RecursiveMixedRadix.digit_decomposition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:13.823927+00:00
-- url     : https://prove2.me/theorems/c342755a-be95-438e-a59a-49c5df9684de
-- title:
--   A telescoping division identity underlying existence.
-- statement:
--   A telescoping division identity underlying existence.
--
--   ```lean
--   theorem RecursiveMixedRadix.digit_decomposition{r : ℕ → ℕ} (n k : ℕ) :
--       n = value r (digit r n) k + (n / weight r k) * weight r k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L167

-- Thm stub generated from NumberTheory/RecursiveMixedRadix.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix

/-!
# Recursive mixed-radix representations

This file isolates the general mixed-radix mechanism behind factoradics and
recursive-base systems.  A radix sequence `r` determines place values
`weight r 0 = 1` and `weight r (k+1) = r k * weight r k`.

The main results prove, constructively and without cardinality arguments, that
valid length-`k` digit strings represent exactly the naturals below
`weight r k`, and do so uniquely.
-/

open RecursiveMixedRadix

open Finset

theorem RecursiveMixedRadix.digit_decomposition{r : ℕ → ℕ} (n k : ℕ) :
    n = value r (digit r n) k + (n / weight r k) * weight r k := by sorry
