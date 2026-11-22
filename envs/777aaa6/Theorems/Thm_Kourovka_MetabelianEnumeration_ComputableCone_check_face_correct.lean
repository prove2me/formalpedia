-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_check_face_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.check_face_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:03.659341+00:00
-- url     : https://prove2.me/theorems/54d2113b-5827-46fc-bab2-a487d7102a7d
-- title:
--   Computable Cone: check face correct
-- statement:
--   The Computable Cone construction uses the check face correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L130-L160
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L130-L160

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.check_face_correct (n r : ℕ) (supports : SupportsCode) (i : Fin n) (sign : ℤ) :
    ((choices r supports).any fun rows =>
      ComputableFourierMotzkin.check n (rows ++ faceRows n i sign)) = true ↔
    ∃ x : Fin n → ℝ, (x i = (sign : ℝ) ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1) ∧
      ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector n u) x ≤ (1 / 2 : ℝ) ^ r := by sorry
