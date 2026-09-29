-- Prove2me | Theorems.Thm_RecursiveMixedRadix_value_lt
-- name    : RecursiveMixedRadix.value_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:20.679973+00:00
-- url     : https://prove2.me/theorems/eb9b5a40-cf73-41ee-bb7b-de3dd81cfd2f
-- title:
--   Valid lower digits always form a number below the next place value.
-- statement:
--   Valid lower digits always form a number below the next place value.
--
--   ```lean
--   theorem RecursiveMixedRadix.value_lt{r c : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
--       (hc : Valid r c k) : value r c k < weight r k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L50

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

theorem RecursiveMixedRadix.value_lt{r c : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
    (hc : Valid r c k) : value r c k < weight r k := by sorry
