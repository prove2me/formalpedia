-- Prove2me | Theorems.Thm_RecursiveMixedRadix_weight_succ
-- name    : RecursiveMixedRadix.weight_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:16.462473+00:00
-- url     : https://prove2.me/theorems/625fe3e0-9175-4289-9b67-d408e97104c1
-- title:
--   Weight succ
-- statement:
--   Formal statement of `RecursiveMixedRadix.weight_succ` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RecursiveMixedRadix.weight_succ(r : ℕ → ℕ) (k : ℕ) :
--       weight r (k + 1) = r k * weight r k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L37

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






@[simp]

theorem RecursiveMixedRadix.weight_succ(r : ℕ → ℕ) (k : ℕ) :
    weight r (k + 1) = r k * weight r k := by sorry
