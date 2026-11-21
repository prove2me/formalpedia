-- Prove2me | solution 1 for Mpfx.ne_zero_of_not_boundOK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:41.47737+00:00
-- url     : https://prove2.me/submissions/49b8d9cf-556f-4cf7-ac75-b398e2295e7f

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
attribute [local simp] Mpfx.Format.boundOK_zero



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {y : Dyadic}
    (h : ¬ Format.boundOK F.b y) : (y : ℝ) ≠ 0 := fun h0 =>
  h (by rw [eq_zero_of_coe_real_zero h0]; exact Format.boundOK_zero _)
end Mpfx
