-- Prove2me | solution 1 for Mpfx.rndDown_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:05:15.399818+00:00
-- url     : https://prove2.me/submissions/d9388b92-834f-414f-9fdc-337b96b023ed

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_rndDown_spec

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) : (rndDown F x : ℝ) ≤ x :=
  (rndDown_spec F x).2.1
end Mpfx
