-- Prove2me | solution 1 for Mpfx.RoundsFinite.eq_zero_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:16:41.27043+00:00
-- url     : https://prove2.me/submissions/0a2a79ab-a851-4965-993a-e2deff3d1f8c

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_FiniteFormat_zero_mem
import Theorems.Thm_Mpfx_Format_zero_mem
attribute [local simp] Mpfx.Dyadic.coe_real_zero



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode}
    {y : Dyadic} (h : RoundsFinite F rm 0 y) : y = 0 :=
  RoundsFinite.eq_of_mem (F.zero_mem) (by rwa [Dyadic.coe_real_zero])
end RoundsFinite
end Mpfx
