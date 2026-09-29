-- Prove2me | Theorems.Thm_RecursiveMixedRadix_digit_valid
-- name    : RecursiveMixedRadix.digit_valid
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:27.700497+00:00
-- url     : https://prove2.me/theorems/125d9431-2b3b-4643-a6cb-d95c2c43f379
-- title:
--   Canonically extracted digits satisfy their local bounds.
-- statement:
--   Canonically extracted digits satisfy their local bounds.
--
--   ```lean
--   theorem RecursiveMixedRadix.digit_valid{r : ℕ → ℕ} (hr : ∀ i, 0 < r i) (n k : ℕ) :
--       Valid r (digit r n) k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L161

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

theorem RecursiveMixedRadix.digit_valid{r : ℕ → ℕ} (hr : ∀ i, 0 < r i) (n k : ℕ) :
    Valid r (digit r n) k := by sorry
