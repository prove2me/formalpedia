-- Prove2me | solution 1 for Mpfx.Cex.no_roundsRAZ_RNE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:50.94079+00:00
-- url     : https://prove2.me/submissions/a38c5f9b-e6e1-45da-a209-be4469ddc577

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
import Theorems.Thm_Mpfx_Cex_alternate_of_adjacent
import Theorems.Thm_Mpfx_Cex_exists_pred
import Theorems.Thm_Mpfx_Cex_le_of_roundsUp_of_isolated
import Theorems.Thm_Mpfx_Cex_roundsRNE_of_bracket
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_rndUp_min
import Theorems.Thm_Mpfx_rndUp_spec
import Theorems.Thm_P2M_Mpfx_Cex_exists_isolated__0de9343c9367
attribute [local simp] Mpfx.Dyadic.coe_real_inj


section
namespace Mpfx
namespace Cex
section Anchors
variable {F₁ : ParityFormat}
private theorem exists_two {F : Format} (h : F.HasPositive 2) :
    ∃ a b : Dyadic, a ∈ F ∧ b ∈ F ∧ (0 : ℝ) < a ∧ (a : ℝ) < b := by
  obtain ⟨f, hmono, hf⟩ := h
  exact ⟨f 0, f 1, (hf 0).1, (hf 1).1, (hf 0).2, hmono (by decide : (0 : Fin 2) < 1)⟩
private theorem boundOK_of_le {F : Format} {z a : Dyadic} (ha : a ∈ F) (hz : 0 ≤ (z : ℝ))
    (hza : (z : ℝ) ≤ a) : Format.boundOK F.b z :=
  boundOK_of_abs_le (by rw [abs_of_nonneg hz, abs_of_nonneg (hz.trans hza)]; exact hza) ha.2.2
private theorem exists_even_upper {a b : Dyadic} (ha : a ∈ F₁.toFormat) (hb : b ∈ F₁.toFormat)
    (ha_pos : (0 : ℝ) < a) (hab : (a : ℝ) < b) :
    ∃ u u' : Dyadic, Adjacent F₁.toFiniteFormat u u' ∧ 0 ≤ (u : ℝ) ∧
      u' ∈ F₁.toFormat ∧ F₁.IsEven u' := by
  obtain ⟨u, hadj, hu0⟩ :=
    exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem hb) (ha_pos.trans hab)
  by_cases heven : F₁.IsEven b
  · exact ⟨u, b, hadj, hu0, hb, heven⟩
  have heven_u : F₁.IsEven u := by
    by_contra h
    exact heven ((alternate_of_adjacent F₁ hadj).2 h)
  have hu_pos : (0 : ℝ) < u := ha_pos.trans_le (hadj.2.2.2 a (mem_unbounded_of_mem ha) hab)
  obtain ⟨u₀, hadj₀, hu₀⟩ := exists_pred F₁.toFiniteFormat hadj.1 hu_pos
  exact ⟨u₀, u, hadj₀, hu₀,
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hb hu0 hadj.2.2.1.le), heven_u⟩
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
theorem _root_.solution (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁.toFiniteFormat (.nearest .toEven) := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨u, u', hadj, hu0, hu', heven⟩ := exists_even_upper ha hb ha_pos hab
  have hlt := hadj.2.2.1
  have hu : u ∈ F₁.toFormat :=
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hu' hu0 hlt.le)
  set m := Dyadic.midpoint u u'
  have hm : (m : ℝ) = ((u : ℝ) + u') / 2 := Dyadic.coe_midpoint u u'
  obtain ⟨K, hK₂, hK₁, hK_le⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat
    (show (0 : ℝ) < m by rw [hm]; linarith)
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKu : (2 : ℝ) ^ K ≤ m - u := by
    have := hK₁.le_abs_sub hadj.1 (fun he => by
      have := (Dyadic.coe_real_inj _ _).mpr he; linarith)
    rwa [abs_of_neg (by linarith), neg_sub] at this
  set x : ℝ := (m : ℝ) - (2 : ℝ) ^ K / 4 with hx
  have hx0 : 0 ≤ x := by linarith
  -- The intermediate RAZ lands in `[m, u']`.
  set z := rndUp F₂ x
  have hz := rndUp_spec F₂ x
  have hz_ge : (m : ℝ) ≤ z := le_of_roundsUp_of_isolated hK₂ hz (by linarith)
  have hz_le : (z : ℝ) ≤ u' := rndUp_min F₂ x (mem_unbounded_of_mem (hsub _ hu')) (by linarith)
  obtain ⟨hzu, hzu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ z) hz_le
  obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
  refine ⟨x, z, u', u,
    ⟨(RoundsFinite.toPositive_iff_awayZero_of_nonneg _ hx0 _).mp hz,
      boundOK_of_le (hsub _ hu') (by linarith) hz_le⟩,
    ⟨roundsRNE_of_bracket hadj (by linarith) hz_le (Or.inr rfl)
      ⟨by rw [hzu, hzu']; linarith, le_rfl⟩ fun _ => heven, hu'.2.2⟩,
    ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inl rfl)
      ⟨le_rfl, by rw [hxu, hxu']; linarith⟩ fun he => by rw [hxu, hxu'] at he; linarith,
      hu.2.2⟩,
    fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩
end Mpfx.Cex
