-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_search_correct
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.search_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:36.440238+00:00
-- url     : https://prove2.me/theorems/9c5800c1-9671-42f8-bbd3-f1cb0db56300
-- title:
--   Cone Verifier: search correct
-- statement:
--   The Cone Verifier construction uses the search correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L37-L59
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L37-L59

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.search_correct {n : ℕ} (epsilon : ℚ) (supports : Supports n)
    (rows : List (Row n)) : search n epsilon supports rows = true ↔
    ∃ x : Fin n → ℝ, Satisfies rows x ∧
      ∀ support ∈ supports, ∃ u ∈ support, dot u x ≤ epsilon := by sorry
