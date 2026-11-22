-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_cubeSphere_ne_zero
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.cubeSphere_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:55.576461+00:00
-- url     : https://prove2.me/theorems/e4e9843d-ed05-44a2-94c7-9d0ae6ceb904
-- title:
--   Cone Verifier: cube Sphere ne zero
-- statement:
--   The Cone Verifier construction uses the cube Sphere ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L156-L160
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L156-L160

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.cubeSphere_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : CubeSphere x) : x ≠ 0 := by sorry
