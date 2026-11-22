-- Prove2me | solution 1 for Mpfx.localDoubleRounding_of_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:39:17.361873+00:00
-- url     : https://prove2.me/submissions/4250a86f-693b-4949-baa1-1bfd7041dac3

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_eq_of_rule
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_abs_faithful_le_of_le
import Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_mem_unbounded_of_mem


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) {B : Bound}
    (hmem : ∀ {T : Dyadic}, T ∈ F₁.unbounded → Format.boundOK B T → T ∈ F₂)
    (rule : ∀ {T : NonNegDyadic}, T.val ∈ F₁.unbounded → Format.boundOK B T.val →
      ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
        RoundsFinite (F₁.withBoundFF T) rm₁ (z : ℝ) w →
        RoundsFinite (F₁.withBoundFF T) rm₁ x w)
    (pin_direct : ∀ {x : ℝ} {y : Dyadic}, RoundsInBound F₁ rm₁ x y → BelowValue F₁ B x)
    (pin_double : ∀ {x : ℝ} {z w : Dyadic}, RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → BelowValue F₁ B x) :
    LocalDoubleRounding F₁ F₂ rm₁ rm₂ (BelowValue F₁ B) where
  pin_direct := pin_direct
  pin_double := pin_double
  bound := fun {_ _} ⟨T, hT, hTB, hxT⟩ hz =>
    boundOK_of_abs_le ((abs_faithful_le_of_le (mem_unbounded_of_mem (hmem hT hTB)) hxT
      hz.isFaithfulRound).trans (le_abs_self _)) (hmem hT hTB).2.2
  agree := fun {x _ _ _} ⟨T, hT, hTB, hxT⟩ hz hw hy => by
    have hzT := abs_faithful_le_of_le (mem_unbounded_of_mem (hmem hT hTB)) hxT
      hz.isFaithfulRound
    have hT0 : (0 : ℚ) ≤ (T : ℚ) := by
      have : (0 : ℝ) ≤ (T : ℝ) := (abs_nonneg x).trans hxT
      exact_mod_cast this
    exact eq_of_rule (B := ((⟨T, hT0⟩ : NonNegDyadic) : Bound)) h₁u
      (rule (T := ⟨T, hT0⟩) hT hTB) hz hw hy
      (boundOK_coe_of_abs_le (abs_faithful_le_of_le hT hzT hw.isFaithfulRound))
      (boundOK_coe_of_abs_le (abs_faithful_le_of_le hT hxT hy.isFaithfulRound))
end Mpfx
