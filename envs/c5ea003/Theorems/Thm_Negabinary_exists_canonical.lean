-- Prove2me | Theorems.Thm_Negabinary_exists_canonical
-- name    : Negabinary.exists_canonical
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:56.983924+00:00
-- url     : https://prove2.me/theorems/a2a3c6b1-cdee-4e48-9d6f-6185dea10ff0
-- title:
--   Every integer has a canonical negabinary representation.
-- statement:
--   Every integer has a canonical negabinary representation.
--
--   ```lean
--   theorem Negabinary.exists_canonical(z : ℤ) :
--       ∃ l : List Bool, Canonical l ∧ value l = z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AlienNumberSystems/Negabinary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AlienNumberSystems/Negabinary.lean#L116

-- Thm stub generated from Applications/AlienNumberSystems/Negabinary.lean
import Mathlib
import Definitions.Def_Applications_AlienNumberSystems_Negabinary

/-!
# Negabinary: unique finite representations of all integers

This file proves that evaluation in radix `-2` gives a bijection between canonical
finite bit strings and the integers. Digits are stored least-significant first.
-/

open Negabinary

theorem Negabinary.exists_canonical(z : ℤ) :
    ∃ l : List Bool, Canonical l ∧ value l = z := by sorry
