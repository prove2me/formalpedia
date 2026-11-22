-- Prove2me | solution 1 for Fpy.reals_mulFmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:56.439665+00:00
-- url     : https://prove2.me/submissions/e0d76c6a-4960-4287-ac86-81f1b7d9ffe4

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Fpy_toReal_mul
import Theorems.Thm_Fpy_precisionAtMost_pHat
import Theorems.Thm_Fpy_precisionAtMost_precMul
import Theorems.Thm_Fpy_Num_mul_eq_finite
import Theorems.Thm_Mpfx_Format_mul_subset
import Theorems.Thm_Mpfx_WithSpecial_mul_eq_finite


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.mul u v ∈ (mulFmt F₁ F₂).reals := by
  obtain ⟨w₁, hw₁, rfl⟩ := hu
  obtain ⟨w₂, hw₂, rfl⟩ := hv
  refine ⟨w₁ * w₂, ?_, (toReal_mul ..).symm⟩
  have hm : w₁ * w₂ ∈ (Format.opMul F₁ F₂).values :=
    Format.mul_subset F₁ F₂ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
  cases h : w₁ * w₂ with
  | finite z =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := WithSpecial.mul_eq_finite.mp h
    change x * y ∈ (Format.opMul F₁ F₂) at hm
    exact ⟨precisionAtMost_precMul (precisionAtMost_pHat hw₁) (precisionAtMost_pHat hw₂),
      hm.2.1, hm.2.2⟩
  | special s =>
    rw [h] at hm
    exact hm
end Fpy
