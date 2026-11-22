-- Prove2me | solution 1 for Mpfx.RoundsFinite.unique_nearest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:50.903545+00:00
-- url     : https://prove2.me/submissions/91736b10-98d7-4827-acac-4e99bb846a4e

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero
import Theorems.Thm_Mpfx_IsFaithfulRound_opposite_sides_of_ne
import Theorems.Thm_Mpfx_isOdd_alternate_of_bracketing
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_FiniteFormat_not_isEven_and_isOdd
attribute [local simp] Mpfx.Dyadic.coe_real_zero



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    (h : ¬ F.IsUndefined (.nearest tb)) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded (.nearest tb) x y₁)
    (h₂ : RoundsFinite F.unbounded (.nearest tb) x y₂) :
    y₁ = y₂ := by
  -- A round-down and a round-up that are equidistant from `x` and distinct
  -- put `x` strictly between them; in particular `x` is neither of them, and
  -- `x ≠ 0` (at `0` both roundings are `0`).
  have ne_of_tie : ∀ {a b : Dyadic}, a ≠ b →
      |x - (a : ℝ)| = |x - (b : ℝ)| → x ≠ (a : ℝ) := by
    intro a b hab hdist hx
    have hzero : |x - (b : ℝ)| = 0 := by rw [← hdist, hx, sub_self, abs_zero]
    exact hab (Dyadic.ext_real (hx.symm.trans (by linarith [abs_eq_zero.mp hzero])))
  cases tb with
  | awayZero =>
    obtain ⟨hm₁, hf₁, hmin₁, htie₁⟩ := h₁
    obtain ⟨hm₂, hf₂, hmin₂, htie₂⟩ := h₂
    by_cases hne : y₁ = y₂
    · exact hne
    exfalso
    have hdist : |x - (y₁ : ℝ)| = |x - (y₂ : ℝ)| :=
      le_antisymm (hmin₁ y₂ hm₂ hf₂) (hmin₂ y₁ hm₁ hf₁)
    -- Each tie-break clause bounds the other's magnitude, so they are equal.
    have habs : |(y₁ : ℝ)| = |(y₂ : ℝ)| :=
      le_antisymm (htie₂ y₁ hm₁ hf₁ hne hdist.symm)
        (htie₁ y₂ hm₂ hf₂ (Ne.symm hne) hdist)
    -- Opposite sides with equal magnitudes: `a = -b`, and equidistance pins
    -- `x = 0`, where both are `0` — contradicting `y₁ ≠ y₂`.
    have key : ∀ {a b : Dyadic}, RoundsFinite F.unbounded .toNegative x a →
        RoundsFinite F.unbounded .toPositive x b → a ≠ b →
        |x - (a : ℝ)| = |x - (b : ℝ)| → |(a : ℝ)| = |(b : ℝ)| → False := by
      intro a b hda hub hab hdist habs'
      have hxa := ne_of_tie hab hdist
      refine (fun hx0 : x = 0 => hxa (by
        have hda0 : RoundsFinite F.unbounded .toNegative 0 a := by rw [← hx0]; exact hda
        rw [hx0, RoundsFinite.eq_zero_of_zero hda0, Dyadic.coe_real_zero])) ?_
      have hle : (a : ℝ) ≤ x := hda.2.1
      have hge : x ≤ (b : ℝ) := hub.2.1
      -- `|a| = |b|` with `a ≠ b` forces `a = -b`, hence `a ≤ 0 ≤ b`.
      have hneg : (a : ℝ) = -(b : ℝ) := by
        rcases abs_eq_abs.mp habs' with hEq | hEq
        · exact absurd (Dyadic.ext_real hEq) hab
        · exact hEq
      rw [hneg] at hle
      -- Equidistance between `-b` and `b` puts `x` at their midpoint, `0`.
      rw [hneg, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - -(b : ℝ)),
          abs_of_nonpos (by linarith : x - (b : ℝ) ≤ 0)] at hdist
      linarith
    rcases hf₁.opposite_sides_of_ne hf₂ hne with ⟨hd, hu⟩ | ⟨hd, hu⟩
    · exact key hd hu hne hdist habs
    · exact key hd hu (Ne.symm hne) hdist.symm habs.symm
  | toEven =>
    obtain ⟨hm₁, hf₁, hmin₁, htie₁⟩ := h₁
    obtain ⟨hm₂, hf₂, hmin₂, htie₂⟩ := h₂
    by_cases hne : y₁ = y₂
    · exact hne
    exfalso
    have hdist : |x - (y₁ : ℝ)| = |x - (y₂ : ℝ)| :=
      le_antisymm (hmin₁ y₂ hm₂ hf₂) (hmin₂ y₁ hm₁ hf₁)
    have hodd : ¬ F.IsUndefined .toOdd := fun ⟨h1, h2, _⟩ => h ⟨h1, h2, Or.inr rfl⟩
    -- Each is a tie for the other, so the tie-break makes both even.
    have even₁ := htie₁ ⟨y₂, hm₂, hf₂, Ne.symm hne, hdist⟩
    have even₂ := htie₂ ⟨y₁, hm₁, hf₁, hne, hdist.symm⟩
    -- But the two neighbours alternate in parity, so they are not both even.
    have key : ∀ {a b : Dyadic}, RoundsFinite F.unbounded .toNegative x a →
        RoundsFinite F.unbounded .toPositive x b → a ≠ b →
        |x - (a : ℝ)| = |x - (b : ℝ)| → F.IsEven a → F.IsEven b → False := by
      intro a b hda hub hab hdist' heva hevb
      exact FiniteFormat.not_isEven_and_isOdd hevb
        ((isOdd_alternate_of_bracketing (F := F.unbounded) hodd hda hub
            (ne_of_tie hab hdist')).mpr
          (fun hoa => FiniteFormat.not_isEven_and_isOdd heva hoa))
    rcases hf₁.opposite_sides_of_ne hf₂ hne with ⟨hd, hu⟩ | ⟨hd, hu⟩
    · exact key hd hu hne hdist even₁ even₂
    · exact key hd hu (Ne.symm hne) hdist.symm even₂ even₁
end RoundsFinite
end Mpfx
