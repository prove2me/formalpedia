-- Prove2me | solution 1 for Mpfx.midpoint_mem_extend_one_of_adjacent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:25.478947+00:00
-- url     : https://prove2.me/submissions/ba70d043-583e-4e71-a68f-b74a8205aa36

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Discrete
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint
import Theorems.Thm_Mpfx_Dyadic_coe_rat_midpoint
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_extend
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_mem_unbounded_of_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_Format_ofIntZpow_mem
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_canonicalExp_eq_of_log_eq
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_exp_le_log_of_mem
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow
import Theorems.Thm_Mpfx_two_zpow_shift

section
namespace Mpfx
private theorem boundOK_midpoint {B : Bound} {y₁ y₂ : _root_.Mpfx.Dyadic}
    (h₁ : Format.boundOK B y₁) (h₂ : Format.boundOK B y₂) :
    Format.boundOK B (_root_.Mpfx.Dyadic.midpoint y₁ y₂) := by
  cases B using Bound.recTopCoe with
  | top => trivial
  | coe B =>
    change |((_root_.Mpfx.Dyadic.midpoint y₁ y₂ : _root_.Mpfx.Dyadic) : ℚ)| ≤ ((B.val : _root_.Mpfx.Dyadic) : ℚ)
    change |((y₁ : _root_.Mpfx.Dyadic) : ℚ)| ≤ ((B.val : _root_.Mpfx.Dyadic) : ℚ) at h₁
    change |((y₂ : _root_.Mpfx.Dyadic) : ℚ)| ≤ ((B.val : _root_.Mpfx.Dyadic) : ℚ) at h₂
    rw [_root_.Mpfx.Dyadic.coe_rat_midpoint, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
    have h_tri : |((y₁ : _root_.Mpfx.Dyadic) : ℚ) + ((y₂ : _root_.Mpfx.Dyadic) : ℚ)|
        ≤ |((y₁ : _root_.Mpfx.Dyadic) : ℚ)| + |((y₂ : _root_.Mpfx.Dyadic) : ℚ)| := abs_add_le _ _
    linarith
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat)
    {y₁ y₂ : _root_.Mpfx.Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : _root_.Mpfx.Dyadic) : ℝ))
    (h_lt : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y₂ : _root_.Mpfx.Dyadic) : ℝ))
    (h_adj : ∀ y : _root_.Mpfx.Dyadic, y ∈ F →
              ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y : _root_.Mpfx.Dyadic) : ℝ) →
              ((y₂ : _root_.Mpfx.Dyadic) : ℝ) ≤ ((y : _root_.Mpfx.Dyadic) : ℝ)) :
    _root_.Mpfx.Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  set m := _root_.Mpfx.Dyadic.midpoint y₁ y₂
  have hm : ((m : _root_.Mpfx.Dyadic) : ℝ) = (((y₁ : _root_.Mpfx.Dyadic) : ℝ) + ((y₂ : _root_.Mpfx.Dyadic) : ℝ)) / 2 :=
    _root_.Mpfx.Dyadic.coe_midpoint y₁ y₂
  set c := F.canonicalExp ((y₁ : _root_.Mpfx.Dyadic) : ℝ)
  set L := Int.log 2 ((y₁ : _root_.Mpfx.Dyadic) : ℝ)
  have hy₂_pos : 0 < ((y₂ : _root_.Mpfx.Dyadic) : ℝ) := h_pos.trans h_lt
  have hlo : (2 : ℝ) ^ L ≤ ((y₁ : _root_.Mpfx.Dyadic) : ℝ) := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) h_pos; exact_mod_cast this
  have hhi : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < (2 : ℝ) ^ (L + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
  -- `y₂ ≤ 2^(L+1)`: that power of two is a value of `F` above `y₁`, or out of bound.
  have hy₂_le : ((y₂ : _root_.Mpfx.Dyadic) : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    by_cases hb : Format.boundOK F.b (_root_.Mpfx.Dyadic.ofIntZpow 1 (L + 1))
    · have hexp : F.exp ≤ ((L + 1 : ℤ) : QExp) := by
        cases he : F.exp using QExp.recBotCoe with
        | bot => exact bot_le
        | coe e =>
          have := exp_le_log_of_mem F he (mem_unbounded_of_mem hy₁F) h_pos
          exact WithBot.coe_le_coe.mpr (by omega)
      have := h_adj _ (Format.ofIntZpow_mem (precisionAtMost_one_zpow F.pos _) hexp hb)
        (by rw [coe_real_ofIntZpow_one]; exact hhi)
      rwa [coe_real_ofIntZpow_one] at this
    · by_contra hgt
      push Not at hgt
      exact hb (boundOK_of_abs_le (by
        rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos two_pos _), abs_of_pos hy₂_pos]
        exact hgt.le) hy₂F.2.2)
  have hm0 : 0 < ((m : _root_.Mpfx.Dyadic) : ℝ) := by rw [hm]; linarith
  have hcm : F.canonicalExp ((m : _root_.Mpfx.Dyadic) : ℝ) = c := by
    refine canonicalExp_eq_of_log_eq F hm0.ne' h_pos.ne' ?_
    rw [abs_of_pos hm0, abs_of_pos h_pos]
    exact log_eq_of_zpow_bounds hm0 (by rw [hm]; linarith) (by rw [hm]; linarith)
  obtain ⟨a, ha⟩ := F.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hy₁F)
  have hc₂ : c ≤ F.canonicalExp ((y₂ : _root_.Mpfx.Dyadic) : ℝ) :=
    F.canonicalExp_mono h_pos.ne' (by rw [abs_of_pos h_pos, abs_of_pos hy₂_pos]; exact h_lt.le)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ((y₂ : _root_.Mpfx.Dyadic) : ℝ) = b * (2 : ℝ) ^ c := by
    obtain ⟨b, hb⟩ := F.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hy₂F)
    exact ⟨_, hb.trans (two_zpow_shift b hc₂)⟩
  have ha' : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) = a * (2 : ℝ) ^ c := ha
  refine mem_of_mem_unbounded_of_boundOK
    ((F.extend 1).mem_unbounded_of_mul_zpow_canonicalExp (m := a + b) ?_)
    (boundOK_midpoint hy₁F.2.2 hy₂F.2.2)
  rw [F.canonicalExp_extend 1 hm0.ne', hcm, hm, ha', hb, zpow_sub₀ two_ne_zero]
  push_cast; field_simp
end Mpfx
