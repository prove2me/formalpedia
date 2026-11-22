-- Prove2me | solution 1 for Mpfx.localDoubleRounding_of_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:40:36.742966+00:00
-- url     : https://prove2.me/submissions/9c65f3b3-8553-4acc-b233-48f322f01953

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_localDoubleRounding_of_below
import Theorems.Thm_Mpfx_exists_mem_above
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_exists_zpow_gt
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_boundOK_boundAfterNext_next
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_le_abs_faithful_of_le
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_nonneg_coe_real
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow
attribute [local simp] Mpfx.Format.boundAfterNext_top



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hmem : ∀ {T : Dyadic}, T ∈ F₁.unbounded →
      Format.boundOK F₁.toFormat.boundAfterNext T → T ∈ F₂)
    (rule : ∀ {T : NonNegDyadic}, T.val ∈ F₁.unbounded →
      Format.boundOK F₁.toFormat.boundAfterNext T.val →
      ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
        RoundsFinite (F₁.withBoundFF T) rm₁ (z : ℝ) w →
        RoundsFinite (F₁.withBoundFF T) rm₁ x w) :
    LocalDoubleRounding F₁ F₂ rm₁ rm₂ (BelowValue F₁ F₁.toFormat.boundAfterNext) := by
  -- Without a bound, some power of two above `|x|` will do.
  have htop : ∀ x : ℝ, F₁.b = ⊤ → BelowValue F₁ F₁.toFormat.boundAfterNext x := by
    intro x hF
    obtain ⟨k, hk, hlt⟩ := Format.exists_zpow_gt |x| F₁.exp
    refine ⟨Dyadic.ofIntZpow 1 k, ⟨precisionAtMost_one_zpow F₁.pos k,
      Dyadic.quantumAtLeast_ofIntZpow hk, trivial⟩, by rw [Format.boundAfterNext_top hF]; trivial,
      by rw [coe_real_ofIntZpow_one]; exact hlt.le⟩
  -- With a bound `b₁`, a value `N` of `F₁` above it, within `next(b₁)`.
  have habove : ∀ b₁ : NonNegDyadic, F₁.b = (b₁ : Bound) →
      ∃ N : Dyadic, N ∈ F₁.unbounded ∧ Format.boundOK F₁.toFormat.boundAfterNext N ∧
        0 ≤ (N : ℝ) ∧ ∀ v : Dyadic, Format.boundOK F₁.b v → |(v : ℝ)| < N := by
    intro b₁ hF
    have hb₁ := nonneg_coe_real b₁
    obtain ⟨N, hN, hbN, hNn⟩ := exists_mem_above (F := F₁) hb₁
    have hnext_nn := (Format.self_le_next F₁.toFormat b₁.val hb₁).trans' hb₁
    refine ⟨N, hN, boundOK_of_abs_le ?_ (boundOK_boundAfterNext_next hF hnext_nn),
      hb₁.trans hbN.le, fun v hv => (abs_coe_real_le_of_boundOK (hF ▸ hv)).trans_lt hbN⟩
    rw [abs_of_nonneg (hb₁.trans hbN.le), abs_of_nonneg hnext_nn]
    exact hNn
  refine localDoubleRounding_of_below h₁u hmem rule (fun {x y} ⟨hy, hby⟩ => ?_)
    (fun {x z w} ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_)
  · rcases hF : F₁.b with _ | b₁
    · exact htop x hF
    obtain ⟨N, hN, hNB, hN0, hlt⟩ := habove b₁ hF
    exact ⟨N, hN, hNB, le_of_lt (lt_of_not_ge fun h =>
      absurd (le_abs_faithful_of_le hN hN0 h hy.isFaithfulRound) (not_le.mpr (hlt y hby)))⟩
  · rcases hF : F₁.b with _ | b₁
    · exact htop x hF
    obtain ⟨N, hN, hNB, hN0, hlt⟩ := habove b₁ hF
    exact ⟨N, hN, hNB, le_of_lt (lt_of_not_ge fun h => absurd (le_abs_faithful_of_le hN hN0
      (le_abs_faithful_of_le (mem_unbounded_of_mem (hmem hN hNB)) hN0 h hz.isFaithfulRound)
      hw.isFaithfulRound) (not_le.mpr (hlt w hbw)))⟩
end Mpfx
