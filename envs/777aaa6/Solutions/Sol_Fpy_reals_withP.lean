-- Prove2me | solution 1 for Fpy.reals_withP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:41.831819+00:00
-- url     : https://prove2.me/submissions/8dcadd14-4f49-4210-b48d-88124229793f

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Mpfx_Format_containsPrec


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F : Format} {p : Prec} (h : F.p ≤ p) {u : Num} (hu : u ∈ F.reals) :
    u ∈ (F.withP p).reals :=
  Format.reals_mono (Format.containsPrec (F₁ := F) (F₂ := F.withP p) h le_rfl le_rfl subset_rfl)
    hu
end Fpy
