-- Prove2me | solution 1 for Mpfx.abs_faithful_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:44:27.584748+00:00
-- url     : https://prove2.me/submissions/7433fa2e-625e-47be-bb58-f5208d885eba

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
    (hN_mem : N ∈ F) (hxN : |x| ≤ (N : ℝ))
    (hfaithful : IsFaithfulRound F x z) :
    |(z : ℝ)| ≤ (N : ℝ) := by
  have hnN_mem : (-N) ∈ F := FiniteFormat.neg_mem hN_mem
  rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
  · have h1 : ((-N : Dyadic) : ℝ) ≤ (z : ℝ) := by
      apply hz_max (-N) hnN_mem
      rw [Dyadic.coe_real_neg]
      have := abs_le.mp hxN
      linarith [this.1]
    rw [Dyadic.coe_real_neg] at h1
    have h2 := abs_le.mp hxN
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h1 : (z : ℝ) ≤ (N : ℝ) := by
      apply hz_min N hN_mem
      have := abs_le.mp hxN
      linarith [this.2]
    have h2 := abs_le.mp hxN
    exact abs_le.mpr ⟨by linarith, by linarith⟩
end Mpfx
