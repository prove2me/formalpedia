-- Prove2me | Theorems.Thm_RecursiveMixedRadix_value_digit
-- name    : RecursiveMixedRadix.value_digit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:48.33544+00:00
-- url     : https://prove2.me/theorems/f902bb38-51c9-4ad6-9a2f-84a523aac50c
-- title:
--   Every natural below the next place value has its canonical representation.
-- statement:
--   Every natural below the next place value has its canonical representation.
--
--   ```lean
--   theorem RecursiveMixedRadix.value_digit{r : ℕ → ℕ} {n k : ℕ}
--       (hn : n < weight r k) : value r (digit r n) k = n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L193

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

theorem RecursiveMixedRadix.value_digit{r : ℕ → ℕ} {n k : ℕ}
    (hn : n < weight r k) : value r (digit r n) k = n := by sorry
