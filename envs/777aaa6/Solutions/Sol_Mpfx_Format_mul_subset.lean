-- Prove2me | solution 1 for Mpfx.Format.mul_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:02:08.917372+00:00
-- url     : https://prove2.me/submissions/538d0994-9388-45e9-9f63-467f355050b4

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
import Theorems.Thm_Mpfx_WithSpecial_mul_eq_finite
import Theorems.Thm_Mpfx_Format_mul_subset_finite
import Theorems.Thm_Mpfx_Format_special_mem_opMul_iff

set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution (F₁ F₂ : Format) :
    F₁.values * F₂.values ⊆ (opMul F₁ F₂).values := by
  rintro w ⟨u, hu, v, hv, rfl⟩
  change u * v ∈ _
  cases h : u * v with
  | finite z =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := WithSpecial.mul_eq_finite.mp h
    exact mul_subset_finite F₁ F₂ ⟨x, hu, y, hv, rfl⟩
  | special s => exact special_mem_opMul_iff.mpr ⟨u, hu, v, hv, h⟩
end Mpfx.Format
