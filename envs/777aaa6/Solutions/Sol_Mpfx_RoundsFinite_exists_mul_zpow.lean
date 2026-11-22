-- Prove2me | solution 1 for Mpfx.RoundsFinite.exists_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:15:12.274856+00:00
-- url     : https://prove2.me/submissions/c27557e3-b5ad-4524-b81c-d805197ec7a9

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndDown_spec
import Theorems.Thm_Mpfx_rndUp_spec
import Theorems.Thm_Mpfx_rndUp_eq
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_or_eq
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y) :
    ∃ c : ℤ, (y : ℝ) = c * (2 : ℝ) ^ F.canonicalExp x := by
  rcases h.isFaithfulRound.eq_or_eq (rndDown_spec F x) (rndUp_spec F x) with rfl | rfl
  · exact ⟨_, by rw [rndDown_eq, Dyadic.coe_ofIntZpow]⟩
  · exact ⟨_, by rw [rndUp_eq, Dyadic.coe_ofIntZpow]⟩
end RoundsFinite
end Mpfx
