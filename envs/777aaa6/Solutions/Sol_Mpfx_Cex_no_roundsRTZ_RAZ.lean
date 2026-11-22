-- Prove2me | solution 1 for Mpfx.Cex.no_roundsRTZ_RAZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:24.482006+00:00
-- url     : https://prove2.me/submissions/a46f01a8-38f8-4dca-ba6e-73b1b31e541b

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
import Theorems.Thm_Mpfx_Cex_roundsDown_of_isolated
import Theorems.Thm_Mpfx_RoundsFinite_self
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_le_rndUp
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_rndUp_min
import Theorems.Thm_Mpfx_rndUp_spec
import Theorems.Thm_P2M_Mpfx_Cex_exists_isolated__0de9343c9367

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
end Anchors
private theorem disagrees_awayZero {F₁ F₂ : FiniteFormat} {rm₂ : RoundingMode} {a b : Dyadic}
    (ha : a ∈ F₁.toFormat) (hb : b ∈ F₁.toFormat) {x : ℝ} (hx0 : 0 ≤ x) (hax : (a : ℝ) < x)
    (hxb : x ≤ b) (hz : RoundsInBound F₂ rm₂ x a) : Disagrees F₂ rm₂ F₁ .awayZero := by
  have hy := rndUp_spec F₁ x
  have hy_ge := le_rndUp F₁ x
  refine ⟨x, a, a, rndUp F₁ x, hz,
    ⟨RoundsFinite.self .awayZero (mem_unbounded_of_mem ha), ha.2.2⟩,
    ⟨(RoundsFinite.toPositive_iff_awayZero_of_nonneg _ hx0 _).mp hy,
      boundOK_of_le hb (by linarith) (rndUp_min F₁ x (mem_unbounded_of_mem hb) hxb)⟩,
    fun h => ?_⟩
  rw [← h] at hy_ge
  linarith
end Cex
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁ .awayZero := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁ ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKb : (2 : ℝ) ^ K ≤ b - a := by
    have := hK₁.le_abs_sub (mem_unbounded_of_mem hb) (fun h => by rw [h] at hab; linarith)
    rwa [abs_of_pos (by linarith)] at this
  exact disagrees_awayZero (x := a + 2 ^ K / 4) ha hb (by linarith) (by linarith) (by linarith)
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ (by linarith) _).mp
      (roundsDown_of_isolated hK₂ (mem_unbounded_of_mem (hsub _ ha)) (by linarith)
        (by linarith)), (hsub _ ha).2.2⟩
end Mpfx.Cex
