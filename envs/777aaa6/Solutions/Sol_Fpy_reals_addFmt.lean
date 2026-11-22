-- Prove2me | solution 1 for Fpy.reals_addFmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:36.038197+00:00
-- url     : https://prove2.me/submissions/5d6b34c3-bdb0-42c6-b98d-9a2bb5675391

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Fpy_reals_opAdd
import Theorems.Thm_Fpy_reals_withP

set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.add u v ∈ (addFmt F₁ F₂).reals :=
  reals_withP le_sup_right (reals_opAdd hu hv)
end Fpy
