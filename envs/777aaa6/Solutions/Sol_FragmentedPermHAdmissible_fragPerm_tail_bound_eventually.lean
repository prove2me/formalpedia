-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPerm_tail_bound_eventually
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:44:31.255029+00:00
-- url     : https://prove2.me/submissions/b82a8aaf-ed46-4740-acd7-3b4974da1bf0

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Fragmented permutations: finite-radius H-admissible saddle data

Fragmented permutations are the labelled class `SET(SEQ_{\ge 1}(Z))`, with EGF
`exp (z / (1 - z))`.  This file packages the finite-radius Hayman data for the
committed `HAdmissible` bridge.  The saddle regime is `r -> 1-`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace FragmentedPermHAdmissible

/-- Denominator `|1-r exp(iθ)|^2`, in a form convenient for tail estimates. -/
def fragPermDenom (r θ : ℝ) : ℝ :=
  (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ)

lemma fragPerm_eventually_Ioo_zero_one :
    ∀ᶠ r : ℝ in fragPermRadFilter, r ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [fragPermRadFilter, eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)] with r hr hleft
  exact ⟨hr.1, hleft⟩

lemma fragPerm_eventually_Ioo_half_one :
    ∀ᶠ r : ℝ in fragPermRadFilter, r ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by
  rw [fragPermRadFilter, eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (by norm_num : ((1 : ℝ) / 2) < 1)
      (by norm_num : (1 : ℝ) < 2)] with r hr hleft
  exact ⟨hr.1, hleft⟩

lemma fragPerm_delta_sq_le_one_sub_sq_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  calc
    (fragPermSaddleDeltaReal r) ^ 2 = (1 - r) ^ (14 / 5 : ℝ) := by
      unfold fragPermSaddleDeltaReal
      rw [← Real.rpow_mul_natCast hu_nonneg (7 / 5 : ℝ) 2]
      norm_num
    _ ≤ (1 - r) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
        (by norm_num : (2 : ℝ) ≤ 14 / 5)
    _ = (1 - r) ^ 2 := by norm_num [Real.rpow_natCast]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma fragPermH_re_circle (r θ : ℝ) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re =
      r * (Real.cos θ - r) / fragPermDenom r θ := by
  unfold fragPermH fragPermDenom
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im, Complex.mul_im]
  simp [Complex.normSq_apply]
  have hcosre : (Complex.cos (θ : ℂ)).re = Real.cos θ := by
    exact (congrArg Complex.re (Complex.ofReal_cos θ)).symm
  have hsinre : (Complex.sin (θ : ℂ)).re = Real.sin θ := by
    exact (congrArg Complex.re (Complex.ofReal_sin θ)).symm
  rw [hcosre, hsinre]
  have hsin : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hnum :
      r * Real.cos θ * (1 - r * Real.cos θ) - (r * Real.sin θ) ^ 2 =
        r * (Real.cos θ - r) := by
    rw [mul_pow, hsin]
    ring
  have hden :
      (1 - r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
    rw [mul_pow, hsin]
    ring
  calc
    _ = (r * Real.cos θ * (1 - r * Real.cos θ) - (r * Real.sin θ) ^ 2) /
        ((1 - r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) := by
      congr 1 <;> ring
    _ = _ := by rw [hnum, hden]

lemma fragPermDenom_pos {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < fragPermDenom r θ := by
  unfold fragPermDenom
  have hu : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hterm : 0 ≤ 2 * r * (1 - Real.cos θ) := by
    have hcos : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    positivity
  nlinarith

lemma fragPermH_real_re (r : ℝ) (hr1 : r < 1) :
    (fragPermH (r : ℂ)).re = r / (1 - r) := by
  unfold fragPermH
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  have hne : 1 - r ≠ 0 := by linarith
  field_simp [hne]

lemma fragPermH_re_drop_eq {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
        (fragPermH (r : ℂ)).re =
      -fragPermSaddleBReal r *
        (((1 - r) ^ 2 * (1 - Real.cos θ)) / fragPermDenom r θ) := by
  rw [fragPermH_re_circle, fragPermH_real_re r hr1]
  have hD : fragPermDenom r θ ≠ 0 := (fragPermDenom_pos hr0 hr1).ne'
  have hu : 1 - r ≠ 0 := by linarith
  unfold fragPermSaddleBReal
  field_simp [hD, hu]
  unfold fragPermDenom
  ring

lemma fragPerm_tail_ratio_lower {r θ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδsq : (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2)
    (hθδ : fragPermSaddleDeltaReal r ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
    fragPermTailRatioC * (fragPermSaddleDeltaReal r) ^ 2 ≤
      ((1 - r) ^ 2 * (1 - Real.cos θ)) / fragPermDenom r θ := by
  let u := 1 - r
  let x := 1 - Real.cos θ
  let δ2 := (fragPermSaddleDeltaReal r) ^ 2
  have hx_nonneg : 0 ≤ x := by dsimp [x]; linarith [Real.cos_le_one θ]
  have hD_pos : 0 < fragPermDenom r θ := fragPermDenom_pos hr0 hr1
  have hδ_nonneg : 0 ≤ fragPermSaddleDeltaReal r := by
    unfold fragPermSaddleDeltaReal
    exact Real.rpow_nonneg (by linarith : 0 ≤ 1 - r) _
  have hδ2_nonneg : 0 ≤ δ2 := sq_nonneg _
  have hk_pos : 0 < 2 / Real.pi ^ 2 := by positivity
  have hA_nonneg : 0 ≤ fragPermTailRatioC := by
    unfold fragPermTailRatioC
    positivity
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθπ
  have hx_lower_k : (2 / Real.pi ^ 2) * δ2 ≤ x := by
    have hθsq : δ2 ≤ θ ^ 2 := by
      calc
        δ2 ≤ |θ| ^ 2 := pow_le_pow_left₀ hδ_nonneg hθδ 2
        _ = θ ^ 2 := by rw [sq_abs]
    dsimp [x]
    calc
      (2 / Real.pi ^ 2) * δ2 ≤ (2 / Real.pi ^ 2) * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hθsq hk_pos.le
      _ ≤ 1 - Real.cos θ := by linarith
  have hA_le_k_half : fragPermTailRatioC ≤ (2 / Real.pi ^ 2) / 2 := by
    unfold fragPermTailRatioC
    field_simp [Real.pi_ne_zero]
    norm_num
  have hx_lower_A : 2 * fragPermTailRatioC * δ2 ≤ x := by
    calc
      2 * fragPermTailRatioC * δ2 ≤ (2 / Real.pi ^ 2) * δ2 := by
        have : 2 * fragPermTailRatioC ≤ 2 / Real.pi ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right this hδ2_nonneg
      _ ≤ x := hx_lower_k
  have hcoef_half :
      (1 / 2 : ℝ) * u ^ 2 ≤ u ^ 2 - 2 * fragPermTailRatioC * r * δ2 := by
    have h2A_r_delta :
        2 * fragPermTailRatioC * r * δ2 ≤ (1 / 2 : ℝ) * u ^ 2 := by
      have h2Aδ_nonneg : 0 ≤ 2 * fragPermTailRatioC * δ2 := by nlinarith
      calc
        2 * fragPermTailRatioC * r * δ2
            = (2 * fragPermTailRatioC * δ2) * r := by ring
        _ ≤ (2 * fragPermTailRatioC * δ2) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hr1]) h2Aδ_nonneg
        _ = 2 * fragPermTailRatioC * 1 * δ2 := by ring
        _ ≤ (1 / 2 : ℝ) * δ2 := by
          have hcoef : 2 * fragPermTailRatioC * 1 ≤ (1 / 2 : ℝ) := by
            unfold fragPermTailRatioC
            have hpi2_ge : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
            have hden_pos : 0 < 3 * Real.pi ^ 2 := by positivity
            field_simp [Real.pi_ne_zero]
            nlinarith
          exact mul_le_mul_of_nonneg_right hcoef hδ2_nonneg
        _ ≤ (1 / 2 : ℝ) * u ^ 2 := by
          exact mul_le_mul_of_nonneg_left (by simpa [u, δ2] using hδsq) (by norm_num)
    nlinarith
  have h2Aδ_nonneg : 0 ≤ 2 * fragPermTailRatioC * δ2 := by nlinarith
  have hmul := mul_le_mul hcoef_half hx_lower_A h2Aδ_nonneg
    (by nlinarith [sq_nonneg u])
  have hmain_num :
      fragPermTailRatioC * δ2 * fragPermDenom r θ ≤ (1 - r) ^ 2 * x := by
    unfold fragPermDenom
    dsimp [u, x, δ2] at hmul hcoef_half hx_lower_A ⊢
    nlinarith
  rw [le_div_iff₀ hD_pos]
  simpa [fragPermDenom, x, δ2, mul_assoc, mul_left_comm, mul_comm] using hmain_num

lemma fragPerm_re_drop_le_neg_tail_scale {r θ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδsq : (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2)
    (hθδ : fragPermSaddleDeltaReal r ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
        (fragPermH (r : ℂ)).re
      ≤ -fragPermTailRatioC * fragPermSaddleBReal r *
          (fragPermSaddleDeltaReal r) ^ 2 := by
  have hratio := fragPerm_tail_ratio_lower hr0 hr1 hδsq hθδ hθπ
  have hb_nonneg : 0 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hu_nonneg : 0 ≤ 1 - r := by linarith
    have hden_nonneg : 0 ≤ (1 - r) ^ 3 := by positivity
    have hnum_nonneg : 0 ≤ r * (1 + r) := by nlinarith [hr0]
    exact div_nonneg hnum_nonneg hden_nonneg
  rw [fragPermH_re_drop_eq hr0 hr1]
  have hmul :
      fragPermTailRatioC * (fragPermSaddleDeltaReal r) ^ 2 *
          fragPermSaddleBReal r ≤
        (((1 - r) ^ 2 * (1 - Real.cos θ)) / fragPermDenom r θ) *
          fragPermSaddleBReal r :=
    mul_le_mul_of_nonneg_right hratio hb_nonneg
  nlinarith

lemma fragPerm_tail_scale_lower {r : ℝ}
    (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) :
    fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ)) ≤
      fragPermTailRatioC * fragPermSaddleBReal r *
        (fragPermSaddleDeltaReal r) ^ 2 := by
  have hrate_nonneg : 0 ≤ (1 - r) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 - r) _
  have hratio_nonneg : 0 ≤ fragPermTailRatioC := by
    unfold fragPermTailRatioC
    positivity
  have hscale :
      fragPermSaddleBReal r * (fragPermSaddleDeltaReal r) ^ 2 =
        r * (1 + r) * (1 - r) ^ (-(1 / 5 : ℝ)) := by
    have hu_pos : 0 < 1 - r := by linarith
    have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
    unfold fragPermSaddleBReal fragPermSaddleDeltaReal
    rw [← Real.rpow_mul_natCast hu_nonneg (7 / 5 : ℝ) 2]
    norm_num
    have hpow3 : (1 - r) ^ 3 = (1 - r) ^ (3 : ℝ) :=
      (Real.rpow_natCast (1 - r) 3).symm
    rw [hpow3]
    rw [div_eq_mul_inv]
    rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
    calc
      r * (1 + r) * (1 - r) ^ (-3 : ℝ) *
          (1 - r) ^ (14 / 5 : ℝ)
          = r * (1 + r) *
              ((1 - r) ^ (-3 : ℝ) * (1 - r) ^ (14 / 5 : ℝ)) := by ring
      _ = r * (1 + r) * (1 - r) ^ (-(1 / 5 : ℝ)) := by
        rw [← Real.rpow_add hu_pos]
        norm_num
  calc
    fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ))
        ≤ ((fragPermTailRatioC) * (3 / 4 : ℝ)) *
            (1 - r) ^ (-(1 / 5 : ℝ)) := by
          have hconst : fragPermTailC ≤ fragPermTailRatioC * (3 / 4 : ℝ) := by
            unfold fragPermTailC fragPermTailRatioC
            field_simp [Real.pi_ne_zero]
            norm_num
          exact mul_le_mul_of_nonneg_right hconst hrate_nonneg
    _ ≤ (fragPermTailRatioC * (r * (1 + r))) *
          (1 - r) ^ (-(1 / 5 : ℝ)) := by
        have hprod : (3 / 4 : ℝ) ≤ r * (1 + r) := by nlinarith [hrhalf]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod hratio_nonneg) hrate_nonneg
    _ = fragPermTailRatioC *
          (r * (1 + r) * (1 - r) ^ (-(1 / 5 : ℝ))) := by ring
    _ = fragPermTailRatioC *
          (fragPermSaddleBReal r * (fragPermSaddleDeltaReal r) ^ 2) := by
            rw [hscale]
    _ = fragPermTailRatioC * fragPermSaddleBReal r *
          (fragPermSaddleDeltaReal r) ^ 2 := by ring

lemma fragPerm_re_drop_le_neg_tail_rate {r θ : ℝ}
    (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1)
    (hδsq : (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2)
    (hθδ : fragPermSaddleDeltaReal r ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
        (fragPermH (r : ℂ)).re
      ≤ -fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ)) := by
  have hr0 : 0 ≤ r := by linarith [hrhalf]
  have hscale := fragPerm_re_drop_le_neg_tail_scale hr0 hr1 hδsq hθδ hθπ
  have hlower := fragPerm_tail_scale_lower hrhalf hr1
  nlinarith

lemma fragPerm_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt fragPermFun r n θ‖ =
      Real.exp
        ((fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
          (fragPermH (r : ℂ)).re) := by
  unfold saddleGAt fragPermFun fragPermH
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) /
          (1 - (r : ℂ) * Complex.exp (↑θ * Complex.I))) /
        Complex.exp ((r : ℂ) / (1 - (r : ℂ))) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        =
      Real.exp
          ((((r : ℂ) * Complex.exp (↑θ * Complex.I)) /
            (1 - (r : ℂ) * Complex.exp (↑θ * Complex.I))).re) /
        Real.exp (((r : ℂ) / (1 - (r : ℂ))).re) := by
          rw [norm_mul, hphase, mul_one, norm_div, Complex.norm_exp, Complex.norm_exp]
    _ =
      Real.exp
        ((((r : ℂ) * Complex.exp (↑θ * Complex.I)) /
            (1 - (r : ℂ) * Complex.exp (↑θ * Complex.I))).re -
          ((r : ℂ) / (1 - (r : ℂ))).re) := by
          rw [← Real.exp_sub]

end FragmentedPermHAdmissible
end

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
theorem solution :
    ∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
      fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt fragPermFun r n θ‖ ≤ fragPermTailE r := by
  filter_upwards [fragPerm_eventually_Ioo_half_one,
    fragPerm_delta_sq_le_one_sub_sq_eventually] with r hr hδsq n θ hθδ hθπ
  rw [fragPerm_saddleGAt_norm]
  unfold fragPermTailE
  exact Real.exp_le_exp.mpr
    (fragPerm_re_drop_le_neg_tail_rate hr.1.le hr.2 hδsq hθδ hθπ)
