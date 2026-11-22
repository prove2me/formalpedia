-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_finite_interval
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.finite_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:57.743553+00:00
-- url     : https://prove2.me/theorems/41bd4bbb-8023-4b1c-92e5-c21003fcea35
-- title:
--   Fourier Motzkin: finite interval
-- statement:
--   The Fourier Motzkin construction uses the finite interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L78-L99
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L78-L99

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.finite_interval {K : Type*} [LinearOrder K] [Zero K]
    (lower upper : List K) :
    (∃ t : K, (∀ l ∈ lower, l ≤ t) ∧ (∀ u ∈ upper, t ≤ u)) ↔
      ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by sorry
