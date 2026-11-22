-- Prove2me | solution 1 for Mpfx.FiniteFormat.abs_le_maxFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:31:50.259635+00:00
-- url     : https://prove2.me/submissions/f913409c-ecdc-4366-b399-e7515aaf9c04

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special
import Theorems.Thm_Mpfx_FiniteFormat_le_maxFinite
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_Format_neg_mem
attribute [local simp] Mpfx.Dyadic.coe_real_neg



set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (hb : F.b ≠ ⊤) {v : Dyadic} (hv : v ∈ F) :
    |(v : ℝ)| ≤ (F.maxFinite hb : ℝ) := by
  refine abs_le.mpr ⟨?_, F.le_maxFinite hb hv⟩
  have h := F.le_maxFinite hb (neg_mem hv)
  rw [Dyadic.coe_real_neg] at h
  linarith
end Mpfx.FiniteFormat
