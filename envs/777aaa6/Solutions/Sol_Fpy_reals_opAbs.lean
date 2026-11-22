-- Prove2me | solution 1 for Fpy.reals_opAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:41.315239+00:00
-- url     : https://prove2.me/submissions/1df6d78d-c691-4342-acc3-648cbd8e4594

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Fpy_toReal_abs
import Theorems.Thm_Mpfx_Format_abs_subset


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.abs u ∈ (Format.opAbs F).reals := by
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨WithSpecial.abs w, Format.abs_subset F ⟨w, hw, rfl⟩, (toReal_abs w).symm⟩
end Fpy
