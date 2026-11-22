-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_badDirection_correct
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.badDirection_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:18.463347+00:00
-- url     : https://prove2.me/theorems/9152b0f3-8ee5-4eda-89aa-83bfe399d932
-- title:
--   Cone Verifier: bad Direction correct
-- statement:
--   The Cone Verifier construction uses the bad Direction correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L113-L129
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L113-L129

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.badDirection_correct {n : ℕ} (supports : Supports n) (epsilon : ℚ) :
    badDirection supports epsilon = true ↔
      ∃ x : Fin n → ℝ, CubeSphere x ∧
        ∀ support ∈ supports, ∃ u ∈ support, dot u x ≤ epsilon := by sorry
