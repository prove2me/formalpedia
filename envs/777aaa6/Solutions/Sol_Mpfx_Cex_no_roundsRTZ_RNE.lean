-- Prove2me | solution 1 for Mpfx.Cex.no_roundsRTZ_RNE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:44.379169+00:00
-- url     : https://prove2.me/submissions/5077300b-d6a7-47b6-90b5-a5543df6e0a0

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
import Theorems.Thm_Mpfx_Cex_alternate_of_adjacent
import Theorems.Thm_Mpfx_Cex_exists_pred
import Theorems.Thm_Mpfx_Cex_le_of_roundsDown_of_isolated
import Theorems.Thm_Mpfx_Cex_roundsRNE_of_bracket
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_rndDown_max
import Theorems.Thm_Mpfx_rndDown_spec
import Theorems.Thm_P2M_Mpfx_Cex_exists_isolated__0de9343c9367
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.FiniteFormat.isEven_zero


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
private theorem exists_even_lower {a : Dyadic} (ha : a ∈ F₁.toFormat) (ha_pos : (0 : ℝ) < a) :
    ∃ u u' : Dyadic, Adjacent F₁.toFiniteFormat u u' ∧ 0 ≤ (u : ℝ) ∧
      u' ∈ F₁.toFormat ∧ F₁.IsEven u := by
  obtain ⟨u, hadj, hu0⟩ := exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem ha) ha_pos
  by_cases heven : F₁.IsEven u
  · exact ⟨u, a, hadj, hu0, ha, heven⟩
  -- `u` is not even, so it is not `0`, and its predecessor is even.
  have hu_pos : (0 : ℝ) < u := hu0.lt_of_ne fun h => heven (by
    rw [Dyadic.ext_real (h.symm.trans Dyadic.coe_real_zero.symm)]
    exact F₁.isEven_zero)
  obtain ⟨u₀, hadj₀, hu₀⟩ := exists_pred F₁.toFiniteFormat hadj.1 hu_pos
  have heven₀ : F₁.IsEven u₀ := by
    by_contra h
    exact heven ((alternate_of_adjacent F₁ hadj₀).2 h)
  exact ⟨u₀, u, hadj₀, hu₀,
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le ha hu0 hadj.2.2.1.le), heven₀⟩
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
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat (.nearest .toEven) := by
  obtain ⟨a, ha, ha_pos⟩ := exists_one h₁
  obtain ⟨u, u', hadj, hu0, hu', heven⟩ := exists_even_lower ha ha_pos
  have hlt := hadj.2.2.1
  have hu : u ∈ F₁.toFormat :=
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hu' hu0 hlt.le)
  set m := Dyadic.midpoint u u'
  have hm : (m : ℝ) = ((u : ℝ) + u') / 2 := Dyadic.coe_midpoint u u'
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat
    (show (0 : ℝ) < m by rw [hm]; linarith)
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKu' : (2 : ℝ) ^ K ≤ u' - m := by
    have := hK₁.le_abs_sub hadj.2.1 (fun he => by
      have := (Dyadic.coe_real_inj _ _).mpr he; linarith)
    rwa [abs_of_pos (by linarith)] at this
  set x : ℝ := (m : ℝ) + (2 : ℝ) ^ K / 4 with hx
  have hx0 : 0 ≤ x := by linarith
  -- The intermediate RTZ lands in `[u, m]`.
  set z := rndDown F₂ x
  have hz := rndDown_spec F₂ x
  have hz_le : (z : ℝ) ≤ m := le_of_roundsDown_of_isolated hK₂ hz (by linarith)
  have hz_ge : (u : ℝ) ≤ z := rndDown_max F₂ x (mem_unbounded_of_mem (hsub _ hu)) (by linarith)
  obtain ⟨hzu, hzu'⟩ := abs_sub_of_bracket hz_ge (by linarith : (z : ℝ) ≤ u')
  obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
  refine ⟨x, z, u, u',
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ hx0 _).mp hz,
      boundOK_of_le (hsub _ hu') (by linarith) (by linarith)⟩,
    ⟨roundsRNE_of_bracket hadj hz_ge (by linarith) (Or.inl rfl)
      ⟨le_rfl, by rw [hzu, hzu']; linarith⟩ fun _ => heven, hu.2.2⟩,
    ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inr rfl)
      ⟨by rw [hxu, hxu']; linarith, le_rfl⟩ fun he => by rw [hxu, hxu'] at he; linarith,
      hu'.2.2⟩,
    fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩
end Mpfx.Cex
