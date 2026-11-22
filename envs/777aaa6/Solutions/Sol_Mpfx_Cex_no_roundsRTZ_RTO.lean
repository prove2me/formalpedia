-- Prove2me | solution 1 for Mpfx.Cex.no_roundsRTZ_RTO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:40.391951+00:00
-- url     : https://prove2.me/submissions/6f899130-da63-436a-b322-ca2fcd06feed

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
import Theorems.Thm_Mpfx_Cex_alternate_of_adjacent
import Theorems.Thm_Mpfx_Cex_exists_pred
import Theorems.Thm_Mpfx_Cex_roundsDown_of_isolated
import Theorems.Thm_Mpfx_ParityFormat_not_isUndefined
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_self
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
import Theorems.Thm_Mpfx_abs_faithful_le_of_le
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_P2M_Mpfx_Cex_exists_isolated__0de9343c9367

section
namespace Mpfx
namespace Cex
section Anchors
variable {F₁ : ParityFormat}
private theorem exists_three {F : Format} (h : F.HasPositive 3) :
    ∃ a b c : Dyadic, a ∈ F ∧ b ∈ F ∧ c ∈ F ∧ (0 : ℝ) < a ∧ (a : ℝ) < b ∧ (b : ℝ) < c := by
  obtain ⟨f, hmono, hf⟩ := h
  exact ⟨f 0, f 1, f 2, (hf 0).1, (hf 1).1, (hf 2).1, (hf 0).2,
    hmono (by decide : (0 : Fin 3) < 1), hmono (by decide : (1 : Fin 3) < 2)⟩
private theorem boundOK_of_le {F : Format} {z a : Dyadic} (ha : a ∈ F) (hz : 0 ≤ (z : ℝ))
    (hza : (z : ℝ) ≤ a) : Format.boundOK F.b z :=
  boundOK_of_abs_le (by rw [abs_of_nonneg hz, abs_of_nonneg (hz.trans hza)]; exact hza) ha.2.2
private theorem exists_not_odd {a b : Dyadic} (ha : a ∈ F₁.toFormat) (hb : b ∈ F₁.toFormat)
    (ha_pos : (0 : ℝ) < a) (hab : (a : ℝ) < b) :
    ∃ h : Dyadic, h ∈ F₁.toFormat ∧ (0 : ℝ) < h ∧ (h : ℝ) ≤ b ∧ ¬ F₁.IsOdd h := by
  obtain ⟨u, hadj, hu0⟩ :=
    exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem hb) (ha_pos.trans hab)
  by_cases hodd : F₁.IsOdd b
  · exact ⟨u, mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hb hu0 hadj.2.2.1.le),
      ha_pos.trans_le (hadj.2.2.2 a (mem_unbounded_of_mem ha) hab), hadj.2.2.1.le,
      (alternate_of_adjacent F₁ hadj).1.mp hodd⟩
  · exact ⟨b, hb, ha_pos.trans hab, le_rfl, hodd⟩
end Anchors
private theorem disagrees_toOdd {F₁ : ParityFormat} {F₂ : FiniteFormat} {rm₂ : RoundingMode}
    {h c : Dyadic} (hh : h ∈ F₁.toFormat) (hh_odd : ¬ F₁.IsOdd h) (hc : c ∈ F₁.toFormat)
    {x : ℝ} (hx0 : 0 ≤ x) (hxc : x ≤ c) (hxh : x ≠ h) (hz : RoundsInBound F₂ rm₂ x h) :
    Disagrees F₂ rm₂ F₁.toFiniteFormat .toOdd := by
  have hy := rndUnbounded_satisfies F₁.toFiniteFormat .toOdd x (F₁.not_isUndefined _)
  have hy_le := abs_faithful_le_of_le (mem_unbounded_of_mem hc)
    (by rwa [abs_of_nonneg hx0]) hy.isFaithfulRound
  refine ⟨x, h, h, _, hz, ⟨RoundsFinite.self .toOdd (mem_unbounded_of_mem hh), hh.2.2⟩,
    ⟨hy, boundOK_of_abs_le (by rwa [abs_of_nonneg (hx0.trans hxc)]) hc.2.2⟩, fun he => ?_⟩
  rw [← he] at hy
  exact hh_odd (hy.2.2 hxh)
end Cex
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 3)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat .toOdd := by
  obtain ⟨a, b, c, ha, hb, hc, ha_pos, hab, hbc⟩ := exists_three h₁
  obtain ⟨h, hh, hh_pos, hhb, hh_odd⟩ := exists_not_odd ha hb ha_pos hab
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat hh_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKc : (2 : ℝ) ^ K ≤ c - h := by
    have := hK₁.le_abs_sub (mem_unbounded_of_mem hc)
      (fun he => by rw [he] at hbc; linarith)
    rwa [abs_of_pos (by linarith)] at this
  exact disagrees_toOdd (x := h + 2 ^ K / 4) hh hh_odd hc (by linarith) (by linarith)
    (by linarith)
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ (by linarith) _).mp
      (roundsDown_of_isolated hK₂ (mem_unbounded_of_mem (hsub _ hh)) (by linarith)
        (by linarith)), (hsub _ hh).2.2⟩
end Mpfx.Cex
