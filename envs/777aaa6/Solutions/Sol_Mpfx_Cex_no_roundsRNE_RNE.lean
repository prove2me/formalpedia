-- Prove2me | solution 1 for Mpfx.Cex.no_roundsRNE_RNE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:58.464197+00:00
-- url     : https://prove2.me/submissions/1091fd3d-ee63-4db0-af3c-6d72e78c71b5

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
import Theorems.Thm_Mpfx_Cex_alternate_of_adjacent
import Theorems.Thm_Mpfx_Cex_exists_pred
import Theorems.Thm_Mpfx_Cex_roundsRNE_of_bracket
import Theorems.Thm_Mpfx_Cex_roundsRNE_of_isolated
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_P2M_Mpfx_Cex_exists_isolated__0de9343c9367
import Theorems.Thm_P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524
attribute [local simp] Mpfx.Dyadic.coe_real_inj


section
namespace Mpfx
namespace Cex
section Anchors
variable {F₁ : ParityFormat}
private theorem exists_one {F : Format} (h : F.HasPositive 1) :
    ∃ a : Dyadic, a ∈ F ∧ (0 : ℝ) < a := by
  obtain ⟨f, -, hf⟩ := h
  exact ⟨f 0, hf 0⟩
private theorem boundOK_of_le {F : Format} {z a : Dyadic} (ha : a ∈ F) (hz : 0 ≤ (z : ℝ))
    (hza : (z : ℝ) ≤ a) : Format.boundOK F.b z :=
  boundOK_of_abs_le (by rw [abs_of_nonneg hz, abs_of_nonneg (hz.trans hza)]; exact hza) ha.2.2
end Anchors
private theorem abs_sub_of_bracket {u u' z : ℝ} (h₁ : u ≤ z) (h₂ : z ≤ u') :
    |z - u| = z - u ∧ |z - u'| = u' - z :=
  ⟨abs_of_nonneg (by linarith), by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)⟩
end Cex
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat (.nearest .toEven) := by
  obtain ⟨u', hu', hu'_pos⟩ := exists_one h₁
  obtain ⟨u, hadj, hu0⟩ :=
    exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem hu') hu'_pos
  have hlt := hadj.2.2.1
  have hu : u ∈ F₁.toFormat :=
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hu' hu0 hlt.le)
  set m := Dyadic.midpoint u u'
  have hm : (m : ℝ) = ((u : ℝ) + u') / 2 := Dyadic.coe_midpoint u u'
  -- `m` is a value of `F₁` with one extra digit, hence of `F₂`.
  have hm₂ : m ∈ F₂.toFormat := by
    have h := midpoint_in_F₁_extend_one_of_F_adjacent (F := F₁.unbounded) hadj.1 hadj.2.1 hlt
      fun v hv hv' => not_lt.mp fun h => by linarith [hadj.2.2.2 v hv h]
    have hb : Format.boundOK F₁.b m :=
      boundOK_of_le hu' (by rw [hm]; linarith) (by rw [hm]; linarith)
    exact hsub _ ⟨h.1, h.2.1, hb⟩
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat
    (show (0 : ℝ) < m by rw [hm]; linarith)
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKu : (2 : ℝ) ^ K ≤ m - u := by
    have := hK₁.le_abs_sub hadj.1 (fun he => by
      have := (Dyadic.coe_real_inj _ _).mpr he; linarith)
    rwa [abs_of_neg (by linarith), neg_sub] at this
  have hm_mid : |(m : ℝ) - u| = |(m : ℝ) - u'| := by
    rw [(abs_sub_of_bracket (by linarith : (u : ℝ) ≤ m) (by linarith : (m : ℝ) ≤ u')).1,
      (abs_sub_of_bracket (by linarith : (u : ℝ) ≤ m) (by linarith : (m : ℝ) ≤ u')).2, hm]
    ring
  have hm_le : (m : ℝ) ≤ u' := by linarith
  have hu_le : (u : ℝ) ≤ m := by linarith
  have hz₂ : ∀ x : ℝ, |x - m| < (2 : ℝ) ^ K / 2 → RoundsInBound F₂ (.nearest .toEven) x m :=
    fun x hx => ⟨roundsRNE_of_isolated hK₂ (mem_unbounded_of_mem hm₂) hx, hm₂.2.2⟩
  by_cases heven : F₁.IsEven u
  · -- The tie at `m` breaks down to `u`; `x` sits above `m`, nearer `u'`.
    set x : ℝ := (m : ℝ) + (2 : ℝ) ^ K / 4 with hx
    obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
    refine ⟨x, m, u, u', hz₂ x (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩),
      ⟨roundsRNE_of_bracket hadj hu_le hm_le (Or.inl rfl) ⟨le_rfl, hm_mid.le⟩
        fun _ => heven, hu.2.2⟩,
      ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inr rfl)
        ⟨by rw [hxu, hxu']; linarith, le_rfl⟩ fun he => by rw [hxu, hxu'] at he; linarith,
        hu'.2.2⟩,
      fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩
  · -- `u'` is even, so the tie breaks up to it; `x` sits below `m`, nearer `u`.
    have heven' := (alternate_of_adjacent F₁ hadj).2 heven
    set x : ℝ := (m : ℝ) - (2 : ℝ) ^ K / 4 with hx
    obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
    refine ⟨x, m, u', u, hz₂ x (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩),
      ⟨roundsRNE_of_bracket hadj hu_le hm_le (Or.inr rfl) ⟨hm_mid.ge, le_rfl⟩
        fun _ => heven', hu'.2.2⟩,
      ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inl rfl)
        ⟨le_rfl, by rw [hxu, hxu']; linarith⟩ fun he => by rw [hxu, hxu'] at he; linarith,
        hu.2.2⟩,
      fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩
end Mpfx.Cex
