-- Prove2me | Theorems.Thm_RecursiveMixedRadix_splitting_div
-- name    : RecursiveMixedRadix.splitting_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:38.979875+00:00
-- url     : https://prove2.me/theorems/92441016-40b4-40ee-9f69-820adc593ee3
-- title:
--   Dividing by the current place value recovers the top digit.
-- statement:
--   Dividing by the current place value recovers the top digit.
--
--   ```lean
--   theorem RecursiveMixedRadix.splitting_div{r c : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
--       (hc : Valid r c (k + 1)) :
--       value r c (k + 1) / weight r k = c k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L77

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

theorem RecursiveMixedRadix.splitting_div{r c : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
    (hc : Valid r c (k + 1)) :
    value r c (k + 1) / weight r k = c k := by sorry
