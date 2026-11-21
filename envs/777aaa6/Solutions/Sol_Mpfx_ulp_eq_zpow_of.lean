-- Prove2me | solution 1 for Mpfx.ulp_eq_zpow_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:46:25.544103+00:00
-- url     : https://prove2.me/submissions/416ef2eb-1eb0-4f7f-a483-6abdb8f8074d

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {x : ℝ} (h : ¬(x = 0 ∧ F.exp = ⊥)) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x := if_neg h
end Mpfx
