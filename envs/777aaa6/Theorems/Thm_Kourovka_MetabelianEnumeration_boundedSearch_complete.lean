-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_boundedSearch_complete
-- name    : Kourovka.MetabelianEnumeration.boundedSearch_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:11.202512+00:00
-- url     : https://prove2.me/theorems/fa135f22-f0d9-496e-b13f-41fceba82c78
-- title:
--   Metabelian Enumeration: bounded Search complete
-- statement:
--   The Metabelian Enumeration construction uses the bounded Search complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L32-L36
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L32-L36

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.boundedSearch_complete (check : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (complete : ∀ p, P p → ∃ c, check p c = true) (p : ℕ) (hp : P p) :
    ∃ n, boundedSearch check p n = true := by sorry
