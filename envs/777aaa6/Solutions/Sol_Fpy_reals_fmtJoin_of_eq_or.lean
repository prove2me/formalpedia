-- Prove2me | solution 1 for Fpy.reals_fmtJoin_of_eq_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:28:00.952681+00:00
-- url     : https://prove2.me/submissions/caff1744-5fee-4fac-b3f5-a66167501546

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops

set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F₁ F₂ : Format} {u v n : Num} (hu : u ∈ F₁.reals)
    (hv : v ∈ F₂.reals) (h : n = u ∨ n = v) : n ∈ (fmtJoin F₁ F₂).reals := by
  rcases h with rfl | rfl
  · exact reals_fmtJoin_left hu F₂
  · exact reals_fmtJoin_right F₁ hv
end Fpy
