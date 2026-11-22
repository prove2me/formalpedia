-- Prove2me | solution 1 for Fpy.precisionAtMost_precMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:33.891171+00:00
-- url     : https://prove2.me/submissions/58c7b987-5eb7-41b6-9d9c-e7ae8b91263b

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Fpy_precisionAtMost_mul_of_one
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mul


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {q₁ q₂ : Prec} {x y : Mpfx.Dyadic}
    (hx : Dyadic.precisionAtMost q₁ x) (hy : Dyadic.precisionAtMost q₂ y) :
    Dyadic.precisionAtMost (precMul q₁ q₂) (x * y) := by
  unfold precMul
  split
  · next h =>
    rcases h with rfl | rfl
    · exact Dyadic.precisionAtMost_mono le_sup_right (precisionAtMost_mul_of_one hx hy)
    · rw [mul_comm]
      exact Dyadic.precisionAtMost_mono le_sup_left (precisionAtMost_mul_of_one hy hx)
  · exact Dyadic.precisionAtMost_mono le_sup_right (Dyadic.precisionAtMost_mul hx hy)
end Fpy
