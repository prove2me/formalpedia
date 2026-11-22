-- Prove2me | solution 1 for Mpfx.RoundsFinite.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:50.763493+00:00
-- url     : https://prove2.me/submissions/3e15ef99-b20c-41de-a457-4dc9bd7a18d7

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone
import Theorems.Thm_Mpfx_RoundsFinite_mono_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_mono_toPositive
import Theorems.Thm_Mpfx_IsFaithfulRound_cross
import Theorems.Thm_Mpfx_IsFaithfulRound_nonneg
import Theorems.Thm_Mpfx_IsFaithfulRound_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_nearest_min
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_awayZero_of_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_toZero_of_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_isOdd_alternate_of_bracketing


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} (h : ¬ F.IsUndefined rm)
    {x x' : ℝ} {y y' : Dyadic} (hx : x ≤ x') (hy : RoundsFinite F.unbounded rm x y)
    (hy' : RoundsFinite F.unbounded rm x' y') : (y : ℝ) ≤ y' := by
  -- Equal inputs round equally; otherwise a crossing pair brackets both in one gap.
  have same : x = x' → (y : ℝ) ≤ y' := fun hxx => by
    subst hxx; rw [RoundsFinite.unique h hy hy']
  cases rm with
  | toNegative => exact mono_toNegative hx hy hy'
  | toPositive => exact mono_toPositive hx hy hy'
  | toZero =>
    rcases le_total 0 x with hx0 | hx0
    · exact mono_toNegative hx ((toNegative_iff_toZero_of_nonneg _ hx0 y).mpr hy)
        ((toNegative_iff_toZero_of_nonneg _ (hx0.trans hx) y').mpr hy')
    rcases le_total x' 0 with hx0' | hx0'
    · exact mono_toPositive hx ((toPositive_iff_toZero_of_nonpos _ (hx.trans hx0') y).mpr hy)
        ((toPositive_iff_toZero_of_nonpos _ hx0' y').mpr hy')
    · exact (hy.isFaithfulRound.nonpos hx0).trans (hy'.isFaithfulRound.nonneg hx0')
  | awayZero =>
    rcases le_total 0 x with hx0 | hx0
    · exact mono_toPositive hx ((toPositive_iff_awayZero_of_nonneg _ hx0 y).mpr hy)
        ((toPositive_iff_awayZero_of_nonneg _ (hx0.trans hx) y').mpr hy')
    rcases le_total x' 0 with hx0' | hx0'
    · exact mono_toNegative hx ((toNegative_iff_awayZero_of_nonpos _ (hx.trans hx0') y).mpr hy)
        ((toNegative_iff_awayZero_of_nonpos _ hx0' y').mpr hy')
    · exact (hy.isFaithfulRound.nonpos hx0).trans (hy'.isFaithfulRound.nonneg hx0')
  | toOdd =>
    rcases eq_or_lt_of_le hx with hxx | hxx
    · exact same hxx
    by_contra hlt
    obtain ⟨-, hu', -, hd', hx'y, hy'x⟩ := hy.2.1.cross hx hy'.2.1 (lt_of_not_ge hlt)
    exact (isOdd_alternate_of_bracketing h hd' hu' (lt_of_le_of_lt hy'x hxx).ne').mp
      (hy.2.2 (lt_of_le_of_lt hx hx'y).ne) (hy'.2.2 (lt_of_le_of_lt hy'x hxx).ne')
  | nearest tb =>
    rcases eq_or_lt_of_le hx with hxx | hxx
    · exact same hxx
    by_contra hlt
    obtain ⟨-, hu', hd, -, hx'y, hy'x⟩ := hy.isFaithfulRound.cross hx hy'.isFaithfulRound
      (lt_of_not_ge hlt)
    have h₁ := hy.nearest_min hd.1 (isFaithfulRound_iff_directed.mpr (.inl hd))
    have h₂ := hy'.nearest_min hu'.1 (isFaithfulRound_iff_directed.mpr (.inr hu'))
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h₁
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h₂
    linarith
end RoundsFinite
end Mpfx
