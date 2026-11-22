-- Prove2me | solution 1 for Fpy.fpyAnalysis_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:44:52.499982+00:00
-- url     : https://prove2.me/submissions/fb0a033c-90f8-494d-bbab-154d34a09bf3

import Definitions.Def_Fpy_FormatInference_Refine
import Definitions.Def_Fpy_FormatInference_Analysis
import Theorems.Thm_Fpy_ctxOfAVal_sound
import Theorems.Thm_Fpy_ArithOp_fmt_sound
import Theorems.Thm_Fpy_ExactOp_aval_sound
import Theorems.Thm_Fpy_fpyCtxFmt_sound
import Theorems.Thm_Fpy_refine_sound


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}
namespace Fpy
theorem _root_.solution (Φ : Program (fpy decode)) : (fpyAnalysis decode c).Sound Φ where
  arith h hop := ArithOp.fmt_sound c h hop
  exact _ hop := ExactOp.aval_sound c hop
  ctxFmt := fpyCtxFmt_sound
  ctxOf := ctxOfAVal_sound
  refine hΓ hκ h := refine_sound hκ _ hΓ h
end Fpy
