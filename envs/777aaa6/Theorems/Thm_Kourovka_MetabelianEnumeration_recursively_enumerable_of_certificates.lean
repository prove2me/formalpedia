-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_recursively_enumerable_of_certificates
-- name    : Kourovka.MetabelianEnumeration.recursively_enumerable_of_certificates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:30.826466+00:00
-- url     : https://prove2.me/theorems/d0b034a6-44d9-4da6-b180-7fc5bfc48530
-- title:
--   Metabelian Enumeration: recursively enumerable of certificates
-- statement:
--   Explicit proof of recursive enumerability from a computable, sound and
--   complete certificate predicate. Instantiating this with Bieri--Strebel
--   certificates is a separate obligation.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L41-L49
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/Enumeration.lean#L41-L49

import Mathlib.Computability.Halting
import Mathlib.Tactic
import Definitions.Def_Kourovka_Computability_Enumeration
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.recursively_enumerable_of_certificates
    (check : ℕ → ℕ → Bool) (hc : Computable₂ check) (P : ℕ → Prop)
    (correct : ∀ p, P p ↔ ∃ c, check p c = true) : REPred P := by sorry
