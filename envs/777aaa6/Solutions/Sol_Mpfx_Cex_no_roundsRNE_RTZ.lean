-- Prove2me | solution 1 for Mpfx.Cex.no_roundsRNE_RTZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:48.977805+00:00
-- url     : https://prove2.me/submissions/8c48fb98-ad53-4bed-bf78-b7e9ff7450b1

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Theorems.Thm_Mpfx_Cex_exists_isolated_le
import Theorems.Thm_Mpfx_Cex_roundsRNE_of_isolated
import Theorems.Thm_Mpfx_RoundsFinite_self
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_nonneg
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_rndDown_le
import Theorems.Thm_Mpfx_rndDown_spec

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
private theorem disagrees_toZero {F₁ F₂ : FiniteFormat} {rm₂ : RoundingMode} {a : Dyadic}
    (ha : a ∈ F₁.toFormat) {x : ℝ} (hx0 : 0 ≤ x) (hxa : x < a)
    (hz : RoundsInBound F₂ rm₂ x a) : Disagrees F₂ rm₂ F₁ .toZero := by
  have hy := rndDown_spec F₁ x
  have hy_le := rndDown_le F₁ x
  refine ⟨x, a, a, rndDown F₁ x, hz,
    ⟨RoundsFinite.self .toZero (mem_unbounded_of_mem ha), ha.2.2⟩,
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ hx0 _).mp hy,
      boundOK_of_le ha (RoundsFinite.toNegative_nonneg hx0 hy) (by linarith)⟩,
    fun h => ?_⟩
  rw [← h] at hy_le
  linarith
end Cex
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F₁ : FiniteFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁ .toZero := by
  obtain ⟨a, ha, ha_pos⟩ := exists_one h₁
  obtain ⟨K, hK, hK_le⟩ := exists_isolated_le F₂ ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  exact disagrees_toZero (x := a - 2 ^ K / 4) ha (by linarith) (by linarith)
    ⟨roundsRNE_of_isolated hK (mem_unbounded_of_mem (hsub _ ha))
      (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩), (hsub _ ha).2.2⟩
end Mpfx.Cex
