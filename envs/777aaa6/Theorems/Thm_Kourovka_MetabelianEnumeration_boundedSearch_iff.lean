-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_boundedSearch_iff
-- name    : Kourovka.MetabelianEnumeration.boundedSearch_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:25.593272+00:00
-- url     : https://prove2.me/theorems/c45c737e-22e8-4142-b59d-43f979c90c9a
-- title:
--   Metabelian Enumeration: bounded Search iff
-- statement:
--   The Metabelian Enumeration construction uses the bounded Search iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L22-L24
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L22-L24

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.boundedSearch_iff (check : ℕ → ℕ → Bool) (p n : ℕ) :
    boundedSearch check p n = true ↔ ∃ c < n, check p c = true := by sorry
