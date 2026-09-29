-- Prove2me | Theorems.Thm_Negabinary_value_injective
-- name    : Negabinary.value_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:53.408582+00:00
-- url     : https://prove2.me/theorems/e9679f3f-0164-4f26-94ab-5d2ed7ea8b66
-- title:
--   Canonical negabinary evaluation is injective.
-- statement:
--   Canonical negabinary evaluation is injective.
--
--   ```lean
--   theorem Negabinary.value_injective{l₁ l₂ : List Bool} (h₁ : Canonical l₁)
--       (h₂ : Canonical l₂) (hv : value l₁ = value l₂) : l₁ = l₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AlienNumberSystems/Negabinary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AlienNumberSystems/Negabinary.lean#L93

-- Thm stub generated from Applications/AlienNumberSystems/Negabinary.lean
import Mathlib
import Definitions.Def_Applications_AlienNumberSystems_Negabinary

/-!
# Negabinary: unique finite representations of all integers

This file proves that evaluation in radix `-2` gives a bijection between canonical
finite bit strings and the integers. Digits are stored least-significant first.
-/

open Negabinary

theorem Negabinary.value_injective{l₁ l₂ : List Bool} (h₁ : Canonical l₁)
    (h₂ : Canonical l₂) (hv : value l₁ = value l₂) : l₁ = l₂ := by sorry
