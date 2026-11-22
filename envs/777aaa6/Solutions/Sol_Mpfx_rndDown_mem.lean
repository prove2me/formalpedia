-- Prove2me | solution 1 for Mpfx.rndDown_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:05:16.500874+00:00
-- url     : https://prove2.me/submissions/feeb0d90-fbed-4ee9-a6cb-362a378886bd

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_spec

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) : rndDown F x ∈ F.unbounded :=
  (rndDown_spec F x).1
end Mpfx
