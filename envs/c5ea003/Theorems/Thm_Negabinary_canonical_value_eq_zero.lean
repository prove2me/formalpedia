-- Prove2me | Theorems.Thm_Negabinary_canonical_value_eq_zero
-- name    : Negabinary.canonical_value_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:49.735385+00:00
-- url     : https://prove2.me/theorems/ed29c070-dd0e-4a9f-829c-ea4c4fe5924f
-- title:
--   A canonical representation of zero is necessarily empty.
-- statement:
--   A canonical representation of zero is necessarily empty.
--
--   ```lean
--   theorem Negabinary.canonical_value_eq_zero{l : List Bool} (hc : Canonical l)
--       (hv : value l = 0) : l = [] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AlienNumberSystems/Negabinary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AlienNumberSystems/Negabinary.lean#L76

-- Thm stub generated from Applications/AlienNumberSystems/Negabinary.lean
import Mathlib
import Definitions.Def_Applications_AlienNumberSystems_Negabinary

/-!
# Negabinary: unique finite representations of all integers

This file proves that evaluation in radix `-2` gives a bijection between canonical
finite bit strings and the integers. Digits are stored least-significant first.
-/

open Negabinary

theorem Negabinary.canonical_value_eq_zero{l : List Bool} (hc : Canonical l)
    (hv : value l = 0) : l = [] := by sorry
