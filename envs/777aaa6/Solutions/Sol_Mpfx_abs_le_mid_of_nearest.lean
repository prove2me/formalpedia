-- Prove2me | solution 1 for Mpfx.abs_le_mid_of_nearest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:35.109531+00:00
-- url     : https://prove2.me/submissions/d1a6ee2c-2a84-484f-a64d-98b3f67421b0

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_IsFaithfulRound_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_nearest_min
import Theorems.Thm_Mpfx_RoundsFinite_neg_nearest
import Theorems.Thm_Mpfx_abs_faithful_le_of_le
import Theorems.Thm_Mpfx_le_abs_faithful_of_le
import Theorems.Thm_P2M_Mpfx_next_extend_midpoint__cd09fcf4dbfc
import Theorems.Thm_P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e
import Theorems.Thm_P2M_Mpfx_next_min__09217aacec9d
attribute [local simp] Mpfx.Dyadic.coe_real_neg


section
namespace Mpfx
private theorem nearest_split {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F.unbounded)
    (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ)) {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (hx : 0 ≤ x) (hy : RoundsFinite F.unbounded (.nearest tb) x y) :
    ((y : ℝ) ≤ d ∧ x ≤ ((F.extend 1).toFormat.next d : ℝ)) ∨
      ((F.toFormat.next d : ℝ) ≤ y ∧ ((F.extend 1).toFormat.next d : ℝ) ≤ x) := by
  have hdN : (d : ℝ) < F.toFormat.next d := Format.lt_next d hd0
  have hN : F.toFormat.next d ∈ F.unbounded := next_mem_unbounded' hd hd0
  rw [next_extend_midpoint' hd0 hguard]
  set N := F.toFormat.next d
  have hgap : ∀ v ∈ F.unbounded, (d : ℝ) < v → (N : ℝ) ≤ v := fun v hv h =>
    next_min' hd hv hd0 hguard h
  have hy0 : 0 ≤ (y : ℝ) := hy.isFaithfulRound.nonneg hx
  rcases le_or_gt x d with hxd | hxd
  · have h := abs_faithful_le_of_le hd (by rwa [abs_of_nonneg hx]) hy.isFaithfulRound
    rw [abs_of_nonneg hy0] at h
    exact Or.inl ⟨h, by linarith⟩
  rcases le_or_gt (N : ℝ) x with hNx | hxN
  · have h := le_abs_faithful_of_le hN (hd0.trans hdN.le) (by rwa [abs_of_nonneg hx])
      hy.isFaithfulRound
    rw [abs_of_nonneg hy0] at h
    exact Or.inr ⟨h, by linarith⟩
  -- `d < x < N`: the faithful roundings are `d` and `N`, and `y` is the nearer.
  have h₁ := hy.nearest_min hd (Or.inl ⟨hd, hxd.le, fun v hv hvx =>
    not_lt.mp fun h => absurd (hgap v hv h) (not_le.mpr (hvx.trans_lt hxN))⟩)
  have h₂ := hy.nearest_min hN (Or.inr ⟨hN, hxN.le, fun v hv hxv => hgap v hv (hxd.trans_le hxv)⟩)
  rw [abs_of_pos (sub_pos.mpr hxd)] at h₁
  rw [abs_of_neg (sub_neg.mpr hxN)] at h₂
  rcases le_or_gt (y : ℝ) d with hyd | hyd
  · rw [abs_of_nonneg (by linarith)] at h₂
    exact Or.inl ⟨hyd, by linarith⟩
  · have hNy := hgap y hy.1 hyd
    rw [abs_of_nonpos (by linarith)] at h₁
    exact Or.inr ⟨hNy, by linarith⟩
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F.unbounded)
    (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ)) {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (hy : RoundsFinite F.unbounded (.nearest tb) x y) (hyd : |(y : ℝ)| ≤ d) :
    |x| ≤ ((F.extend 1).toFormat.next d : ℝ) := by
  wlog hx : 0 ≤ x generalizing x y
  · have h := this ((RoundsFinite.neg_nearest _ tb x y).mp hy)
      (by rwa [Dyadic.coe_real_neg, abs_neg]) (by linarith)
    rwa [abs_neg] at h
  have hdN : (d : ℝ) < F.toFormat.next d := Format.lt_next d hd0
  rcases nearest_split hd hd0 hguard hx hy with ⟨-, h⟩ | ⟨h, -⟩
  · rwa [abs_of_nonneg hx]
  · linarith [le_abs_self (y : ℝ)]
end Mpfx
