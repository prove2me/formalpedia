-- Prove2me | solution 1 for Mpfx.le_abs_faithful_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:44:29.205373+00:00
-- url     : https://prove2.me/submissions/dd49eb91-c965-457e-b527-88603e4e9a4a

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_Format_neg_mem
attribute [local simp] Mpfx.Dyadic.coe_real_neg



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F) (hN_nn : 0 ≤ (N : ℝ)) (hxN : (N : ℝ) ≤ |x|)
    (hf : IsFaithfulRound F x z) : (N : ℝ) ≤ |(z : ℝ)| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at hxN
    rcases hf with ⟨-, -, hmax⟩ | ⟨-, hxz, -⟩
    · exact (hmax N hN_mem hxN).trans (le_abs_self _)
    · exact (hxN.trans hxz).trans (le_abs_self _)
  · rw [abs_of_neg hx] at hxN
    rcases hf with ⟨-, hzx, -⟩ | ⟨-, -, hmin⟩
    · rw [abs_of_nonpos (by linarith)]; linarith
    · have h := hmin (-N) (FiniteFormat.neg_mem hN_mem)
        (by rw [Dyadic.coe_real_neg]; linarith)
      rw [Dyadic.coe_real_neg] at h
      rw [abs_of_nonpos (by linarith)]; linarith
end Mpfx
