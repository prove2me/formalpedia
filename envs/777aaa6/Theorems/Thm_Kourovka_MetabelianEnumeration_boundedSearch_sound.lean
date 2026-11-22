-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_boundedSearch_sound
-- name    : Kourovka.MetabelianEnumeration.boundedSearch_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:07.739709+00:00
-- url     : https://prove2.me/theorems/b44a13f3-8723-40eb-9e98-1eb40a112b44
-- title:
--   Metabelian Enumeration: bounded Search sound
-- statement:
--   The Metabelian Enumeration construction uses the bounded Search sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L26-L30
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L26-L30

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.boundedSearch_sound (check : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (sound : ∀ p c, check p c = true → P p) (p n : ℕ)
    (h : boundedSearch check p n = true) : P p := by sorry
