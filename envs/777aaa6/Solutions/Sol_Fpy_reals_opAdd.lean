-- Prove2me | solution 1 for Fpy.reals_opAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:40.301213+00:00
-- url     : https://prove2.me/submissions/d0abbca4-71f5-4118-9075-8b4678726ec9

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Fpy_toReal_add
import Theorems.Thm_Mpfx_Format_add_subset


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.add u v ∈ (Format.opAdd F₁ F₂).reals := by
  obtain ⟨w₁, hw₁, rfl⟩ := hu
  obtain ⟨w₂, hw₂, rfl⟩ := hv
  exact ⟨w₁ + w₂, Format.add_subset F₁ F₂ ⟨w₁, hw₁, w₂, hw₂, rfl⟩, (toReal_add ..).symm⟩
end Fpy
