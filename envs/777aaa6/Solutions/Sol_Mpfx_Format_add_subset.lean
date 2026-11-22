-- Prove2me | solution 1 for Mpfx.Format.add_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:50.795691+00:00
-- url     : https://prove2.me/submissions/19d53118-b51f-448f-93eb-6ea231da324e

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
import Theorems.Thm_Mpfx_WithSpecial_add_eq_finite
import Theorems.Thm_Mpfx_Format_add_subset_finite
import Theorems.Thm_Mpfx_Format_special_mem_opAdd_iff

set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution (F₁ F₂ : Format) :
    F₁.values + F₂.values ⊆ (opAdd F₁ F₂).values := by
  rintro w ⟨u, hu, v, hv, rfl⟩
  change u + v ∈ _
  cases h : u + v with
  | finite z =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := WithSpecial.add_eq_finite.mp h
    exact add_subset_finite F₁ F₂ ⟨x, hu, y, hv, rfl⟩
  | special s => exact special_mem_opAdd_iff.mpr ⟨u, hu, v, hv, h⟩
end Mpfx.Format
