-- Prove2me | solution 1 for Mpfx.abs_ne_of_toOdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:58.488169+00:00
-- url     : https://prove2.me/submissions/ce0748bc-b152-4053-8af5-fd9fbe64c939

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_Format_extend_one_extend_one_subset_extend_two
import Theorems.Thm_Mpfx_Format_neg_mem
import Theorems.Thm_Mpfx_toOdd_notMem_of_extend_subset
attribute [local simp] Mpfx.Dyadic.coe_real_neg



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F₂.unbounded .toOdd x z) (hxz : x ≠ (z : ℝ)) {v : Dyadic}
    (hv : v ∈ (F₁.extend 1).unbounded)
    (hvB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext v) :
    |(z : ℝ)| ≠ |(v : ℝ)| := by
  have hnot : z ∉ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    apply toOdd_notMem_of_extend_subset (F₂ := F₂.unbounded) ?_ hp_F₂ hz hxz
    exact ((Format.extend_one_extend_one_subset_extend_two
      (F₁.toFormat.withBound ((F₁.extend 1).toFormat.boundAfterNext))).trans hsub).trans
      F₂.subset_unbounded
  have hvG : v ∈ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := ⟨hv.1, hv.2.1, hvB⟩
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hnot (Dyadic.ext_real h ▸ hvG)
  · have hzv : z = -v := Dyadic.ext_real (by rw [h, Dyadic.coe_real_neg])
    exact hnot (by rw [hzv]; exact FiniteFormat.neg_mem hvG)
end Mpfx
