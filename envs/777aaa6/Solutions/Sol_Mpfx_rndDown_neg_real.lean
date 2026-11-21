-- Prove2me | solution 1 for Mpfx.rndDown_neg_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:38.611569+00:00
-- url     : https://prove2.me/submissions/1e4c8fc6-55f5-4f59-b05d-5df6002596f8

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndUp_eq
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_canonicalExp_neg
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) :
    (rndDown F (-x) : ℝ) = -(rndUp F x : ℝ) := by
  rw [rndDown_eq, rndUp_eq, Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow, canonicalExp_neg,
      show (-x) * (2 : ℝ) ^ (-(F.canonicalExp x)) = -(x * (2 : ℝ) ^ (-(F.canonicalExp x)))
        from by ring, Int.floor_neg]
  push_cast; ring
end Mpfx
