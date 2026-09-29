-- Prove2me | Theorems.Thm_RecursiveMixedRadix_value_unique
-- name    : RecursiveMixedRadix.value_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:50:33.860429+00:00
-- url     : https://prove2.me/theorems/129d7fcb-9985-4add-ad83-8d29d0e59aa2
-- title:
--   Direct uniqueness of bounded mixed-radix representations.
-- statement:
--   Direct uniqueness of bounded mixed-radix representations.
--
--   ```lean
--   theorem RecursiveMixedRadix.value_unique{r c d : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
--       (hc : Valid r c k) (hd : Valid r d k)
--       (hv : value r c k = value r d k) : ∀ i < k, c i = d i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RecursiveMixedRadix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RecursiveMixedRadix.lean#L101

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

theorem RecursiveMixedRadix.value_unique{r c d : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
    (hc : Valid r c k) (hd : Valid r d k)
    (hv : value r c k = value r d k) : ∀ i < k, c i = d i := by sorry
