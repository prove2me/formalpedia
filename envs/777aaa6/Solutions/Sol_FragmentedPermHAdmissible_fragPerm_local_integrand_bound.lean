-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPerm_local_integrand_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:09:18.760413+00:00
-- url     : https://prove2.me/submissions/bc0ab163-0123-4415-ae93-e88f47f390dd

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
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
section
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

lemma fragPerm_sqrt_b_lower_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)) ≤
      Real.sqrt (fragPermSaddleBReal r) := by
  let u : ℝ := 1 - r
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hden_pos : 0 < u ^ 3 := by positivity
  have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
  have hb_lower : (1 / 2 : ℝ) / u ^ 3 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hden_pos ⊢
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hx_sq : ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2 ≤
      fragPermSaddleBReal r := by
    calc
      ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2
          = (1 / 4 : ℝ) * u ^ (-(3 : ℝ)) := by
            rw [mul_pow]
            norm_num
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
      _ ≤ (1 / 2 : ℝ) * u ^ (-(3 : ℝ)) := by
            have hpow_nonneg : 0 ≤ u ^ (-(3 : ℝ)) := Real.rpow_nonneg hu_nonneg _
            nlinarith
      _ = (1 / 2 : ℝ) / u ^ 3 := by
            rw [Real.rpow_neg hu_nonneg]
            have hu3 : u ^ (3 : ℝ) = u ^ 3 := by
              norm_num [Real.rpow_natCast]
            rw [hu3]
            ring
      _ ≤ fragPermSaddleBReal r := hb_lower
  have hsqrt := Real.le_sqrt_of_sq_le hx_sq
  simpa [u] using hsqrt

lemma fragPerm_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ =
      Complex.exp (fragPermLocalExponent r θ) := by
  unfold saddleLocalRatio fragPermFun fragPermLocalExponent
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  ring

lemma fragPerm_exp_i_sub_one_norm_le_two_abs {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ 2 * |θ| := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_le (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
  simpa [hw] using h

lemma fragPerm_exp_i_sub_one_sub_id_norm_le_sq {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ |θ| ^ 2 := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_sub_id_le
    (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
  simpa [hw] using h

lemma fragPermLocalExponent_decomp {r θ : ℝ} (hr1 : r < 1)
    (hy : (1 : ℂ) -
        (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) - 1) / (1 - (r : ℂ)) ≠ 0) :
    let u : ℂ := 1 - (r : ℂ)
    let w : ℂ := (θ : ℂ) * Complex.I
    let q : ℂ := Complex.exp w - 1
    let y : ℂ := (r : ℂ) * q / u
    fragPermLocalExponent r θ =
      ((r : ℂ) / u ^ 2) * ExpStirling.expLocalRemainder θ +
        (((r : ℂ) ^ 2 / u ^ 3) * (q ^ 2 - w ^ 2)) +
          (((r : ℂ) ^ 3 / u ^ 4) * q ^ 3 * (1 - y)⁻¹) := by
  dsimp
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  have hu_ne : u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [u] at hre
    linarith
  have hmain_den : (1 : ℂ) - (r : ℂ) * Complex.exp w ≠ 0 := by
    intro hzero
    apply hy
    have heq :
        (1 : ℂ) -
            (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) - 1) / (1 - (r : ℂ)) =
          ((1 : ℂ) - (r : ℂ) * Complex.exp w) / (1 - (r : ℂ)) := by
      change (1 : ℂ) - (r : ℂ) * (Complex.exp w - 1) / (1 - (r : ℂ)) =
        ((1 : ℂ) - (r : ℂ) * Complex.exp w) / (1 - (r : ℂ))
      field_simp [hu_ne]
      have haux : (1 : ℂ) + (r : ℂ) * (1 - (r : ℂ))⁻¹ =
          (1 - (r : ℂ))⁻¹ := by
        have hurne : (1 - r : ℝ) ≠ 0 := by linarith
        have hreal : (1 : ℝ) + r * (1 - r)⁻¹ = (1 - r)⁻¹ := by
          field_simp [hurne]
          ring
        exact_mod_cast hreal
      linear_combination haux
    rw [heq, hzero]
    simp
  have huq_ne : u - (r : ℂ) * q ≠ 0 := by
    have hden_eq : (1 : ℂ) - (r : ℂ) * Complex.exp w = u - (r : ℂ) * q := by
      dsimp [u, q]
      ring
    rwa [hden_eq] at hmain_den
  have hdiff :
      fragPermH ((r : ℂ) * Complex.exp w) - fragPermH (r : ℂ) =
        (r : ℂ) * q / (u * (u - (r : ℂ) * q)) := by
    have hrat {a q u : ℂ} (hu : u = 1 - a) (huq : u - a * q ≠ 0) (hu0 : u ≠ 0) :
        a * (1 + q) / (1 - a * (1 + q)) - a / (1 - a) =
          a * q / (u * (u - a * q)) := by
      subst u
      have h1 : (1 : ℂ) - a ≠ 0 := hu0
      have h2 : (1 : ℂ) - a * (1 + q) ≠ 0 := by
        simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using huq
      field_simp [h1, h2]
      ring
    have hexp : Complex.exp w = 1 + q := by
      dsimp [q]
      ring
    unfold fragPermH
    rw [hexp]
    exact hrat (a := (r : ℂ)) (q := q) (u := u) rfl huq_ne hu_ne
  have hgeom :
      (r : ℂ) * q / (u * (u - (r : ℂ) * q)) =
        ((r : ℂ) / u ^ 2) * q +
          (((r : ℂ) ^ 2 / u ^ 3) * q ^ 2) +
            (((r : ℂ) ^ 3 / u ^ 4) * q ^ 3 *
              (1 - (r : ℂ) * q / u)⁻¹) := by
    field_simp [hu_ne, huq_ne, hy]
    ring
  have hq :
      q = w - ((θ ^ 2 / 2 : ℝ) : ℂ) + ExpStirling.expLocalRemainder θ := by
    dsimp [q, w]
    rw [ExpStirling.expLocalRemainder_eq]
    ring
  have hlin :
      ((fragPermSaddleAReal r * θ : ℝ) : ℂ) * Complex.I =
        ((r : ℂ) / u ^ 2) * w := by
    unfold fragPermSaddleAReal
    dsimp [u, w]
    have hurne : (1 - r : ℝ) ≠ 0 := by linarith
    field_simp [hurne]
    norm_num [Complex.ext_iff]
  have hquad :
      ((fragPermSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ) =
        ((r : ℂ) / u ^ 2) * (((θ ^ 2 / 2 : ℝ) : ℂ)) -
          (((r : ℂ) ^ 2 / u ^ 3) * (w ^ 2)) := by
    unfold fragPermSaddleBReal
    dsimp [u, w]
    have hurne : (1 - r : ℝ) ≠ 0 := by linarith
    have hw2 : ((θ : ℂ) * Complex.I) ^ 2 = -((θ ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq]
      norm_num
    rw [hw2]
    have hreal : r * (1 + r) / (1 - r) ^ 3 * θ ^ 2 / 2 =
        r / (1 - r) ^ 2 * (θ ^ 2 / 2) - (r ^ 2 / (1 - r) ^ 3) * (-(θ ^ 2)) := by
      field_simp [hurne]
      ring
    exact_mod_cast hreal
  unfold fragPermLocalExponent
  rw [hdiff, hgeom]
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let C : ℂ := (r : ℂ) ^ 3 / u ^ 4 * q ^ 3 * (1 - (r : ℂ) * q / u)⁻¹
  let T : ℂ := ((θ ^ 2 / 2 : ℝ) : ℂ)
  change A * q + B * q ^ 2 + C -
      ((fragPermSaddleAReal r * θ : ℝ) : ℂ) * Complex.I +
        ((fragPermSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ) =
    A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C
  rw [hlin, hquad]
  change A * q + B * q ^ 2 + C - A * w + (A * T - B * w ^ 2) =
    A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C
  rw [hq]
  ring

end FragmentedPermHAdmissible
end
end

/-!
# Second-order saddle data for fragmented permutations

This file adds the second-order correction layer for
`exp (z / (1 - z))`.  The logarithmic saddle derivatives are
`b₃(r) = r(1 + 4r + r²)/(1-r)^4` and
`b₄(r) = r(1 + 11r + 11r² + r³)/(1-r)^5`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace FragmentedPermHAdmissible

private def expLocalRemainderFifth (θ : ℝ) : ℂ :=
  ExpStirling.expLocalRemainder θ -
    ((((θ : ℂ) * Complex.I) ^ 3) / (((3 : ℕ).factorial : ℕ) : ℂ) +
      (((θ : ℂ) * Complex.I) ^ 4) / (((4 : ℕ).factorial : ℕ) : ℂ))

private lemma expLocalRemainderFifth_norm_le {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖expLocalRemainderFifth θ‖ ≤ Real.exp 2 * |θ| ^ 5 := by
  let u : ℂ := (θ : ℂ) * Complex.I
  have htail := Complex.norm_exp_sub_sum_le_norm_mul_exp u 5
  have hnorm : ‖u‖ = |θ| := by simp [u]
  have hleft :
      ExpStirling.expLocalRemainder θ -
          (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
            u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ)) =
        Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ) := by
    simp [ExpStirling.expLocalRemainder, u, Finset.sum_range_succ]
    ring
  change
    ‖ExpStirling.expLocalRemainder θ -
        (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
          u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ))‖ ≤
      Real.exp 2 * |θ| ^ 5
  rw [hleft]
  calc
    ‖Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ)‖
        ≤ ‖u‖ ^ 5 * Real.exp ‖u‖ := htail
    _ = |θ| ^ 5 * Real.exp |θ| := by rw [hnorm]
    _ ≤ |θ| ^ 5 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 5)
    _ = Real.exp 2 * |θ| ^ 5 := by ring

private def fragPermScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((fragPermSaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def fragPermScaledQuartic (r x : ℝ) : ℂ :=
  ((fragPermSaddleB4Real r : ℂ) / (24 * (fragPermSaddleBReal r : ℂ) ^ 2)) *
    (x : ℂ) ^ 4

private def fragPermScaledRemainder (r x : ℝ) : ℂ :=
  fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
    fragPermScaledCubic r x - fragPermScaledQuartic r x

private lemma fragPermLocalExponent_scaled_split (r x : ℝ) :
    fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) =
      fragPermScaledCubic r x + fragPermScaledQuartic r x +
        fragPermScaledRemainder r x := by
  unfold fragPermScaledRemainder
  ring

private lemma fragPerm_sqrtB_sq {r : ℝ} (hb : 0 < fragPermSaddleBReal r) :
    ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) =
      (fragPermSaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private lemma fragPerm_saddleSecondPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < fragPermSaddleBReal r) :
    saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x =
      1 + fragPermScaledCubic r x + fragPermScaledQuartic r x +
        (fragPermScaledCubic r x) ^ 2 / 2 := by
  have hsqrt_sq := fragPerm_sqrtB_sq hb
  have hsqrt_ne : (Real.sqrt (fragPermSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (fragPermSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
        (fragPermSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  unfold saddleSecondPoly fragPermScaledCubic fragPermScaledQuartic
  field_simp [hsqrt_ne, hb_ne]
  ring_nf
  rw [hsqrt_pow6, Complex.I_sq]
  norm_num [Complex.ofReal_pow]
  ring

private lemma complex_exp_second_error_bound (C Q R W : ℂ)
    (hW : W = C + Q + R) (hWnorm : ‖W‖ ≤ 1) :
    ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
      Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
        (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
  have hsum :
      (∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)) =
        1 + W + W ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  have htail :
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ ≤ Real.exp 1 * ‖W‖ ^ 3 := by
    calc
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ =
          ‖Complex.exp W - ∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)‖ := by
            rw [hsum]
      _ ≤ ‖W‖ ^ 3 * Real.exp ‖W‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp W 3
      _ ≤ ‖W‖ ^ 3 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hWnorm) (pow_nonneg (norm_nonneg W) 3)
      _ = Real.exp 1 * ‖W‖ ^ 3 := by ring
  have hdecomp :
      Complex.exp W - (1 + C + Q + C ^ 2 / 2) =
        (Complex.exp W - (1 + W + W ^ 2 / 2)) +
          (R + (W ^ 2 - C ^ 2) / 2) := by
    rw [hW]
    ring
  rw [hdecomp]
  calc
    ‖(Complex.exp W - (1 + W + W ^ 2 / 2)) + (R + (W ^ 2 - C ^ 2) / 2)‖
        ≤ ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ +
            ‖R + (W ^ 2 - C ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R + (W ^ 2 - C ^ 2) / 2‖ :=
      add_le_add htail (le_refl _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖(W ^ 2 - C ^ 2) / 2‖) := by
      exact add_le_add (le_refl _) (norm_add_le _ _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖W ^ 2 - C ^ 2‖) := by
      have hhalf : ‖(W ^ 2 - C ^ 2) / 2‖ ≤ ‖W ^ 2 - C ^ 2‖ := by
        rw [norm_div, Complex.norm_ofNat]
        norm_num
      exact add_le_add (le_refl _) (add_le_add_right hhalf _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
          (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
      have hsq :
          W ^ 2 - C ^ 2 = (Q + R) * (2 * C + Q + R) := by
        rw [hW]
        ring
      have hprod :
          ‖W ^ 2 - C ^ 2‖ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
        rw [hsq]
        calc
          ‖(Q + R) * (2 * C + Q + R)‖ =
              ‖Q + R‖ * ‖2 * C + Q + R‖ := by rw [norm_mul]
          _ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
            have hQR : ‖Q + R‖ ≤ ‖Q‖ + ‖R‖ := norm_add_le _ _
            have h2C : ‖(2 : ℂ) * C‖ = 2 * ‖C‖ := by
              rw [norm_mul, Complex.norm_ofNat]
            have hCQR : ‖2 * C + Q + R‖ ≤ 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by
              calc
                ‖2 * C + Q + R‖ ≤ ‖2 * C + Q‖ + ‖R‖ := norm_add_le _ _
                _ ≤ (‖2 * C‖ + ‖Q‖) + ‖R‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
                _ = 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by rw [h2C]
            exact mul_le_mul hQR hCQR (norm_nonneg _) (by positivity)
      nlinarith [hprod]

private lemma fragPermSaddleBReal_pos_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    0 < fragPermSaddleBReal r := by
  unfold fragPermSaddleBReal
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hnum : 0 < r * (1 + r) := by positivity
  have hden : 0 < (1 - r) ^ 3 := by positivity
  exact div_pos hnum hden

private lemma fragPermScaledCubic_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermScaledCubic r x‖ ≤ 10 * Real.sqrt (1 - r) * |x| ^ 3 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hr0 : 0 ≤ r := hrpos.le
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := fragPermSaddleBReal_pos_of_Ioo_half_one hr
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hb3_nonneg : 0 ≤ fragPermSaddleB3Real r := by
    unfold fragPermSaddleB3Real
    positivity
  have hcoef_eq :
      ‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖ =
        fragPermSaddleB3Real r / (6 * (Real.sqrt (fragPermSaddleBReal r)) ^ 3) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb3_nonneg]
    simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hsqrt_pos]
  have hcoef_sq :
      (‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖) ^ 2
        ≤ (10 * Real.sqrt u) ^ 2 := by
    rw [hcoef_eq]
    have hb_sq : (Real.sqrt (fragPermSaddleBReal r)) ^ 2 = fragPermSaddleBReal r :=
      Real.sq_sqrt hbpos.le
    have hsqrt6 :
        (Real.sqrt (fragPermSaddleBReal r)) ^ 6 = fragPermSaddleBReal r ^ 3 := by
      calc
        (Real.sqrt (fragPermSaddleBReal r)) ^ 6 =
            ((Real.sqrt (fragPermSaddleBReal r)) ^ 2) ^ 3 := by ring
        _ = fragPermSaddleBReal r ^ 3 := by rw [hb_sq]
    unfold fragPermSaddleBReal fragPermSaddleB3Real
    dsimp [u] at hu_pos ⊢
    rw [show (fragPermSaddleBReal r) = r * (1 + r) / (1 - r) ^ 3 by rfl] at hsqrt6
    rw [show (r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 /
          (6 * Real.sqrt (r * (1 + r) / (1 - r) ^ 3) ^ 3)) ^ 2 =
        (r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4) ^ 2 /
          (36 * Real.sqrt (r * (1 + r) / (1 - r) ^ 3) ^ 6) by ring]
    rw [hsqrt6]
    rw [show (10 * Real.sqrt (1 - r)) ^ 2 = 100 * (1 - r) by
      rw [mul_pow, Real.sq_sqrt (by linarith [hr.2] : 0 ≤ 1 - r)]
      ring]
    have hden_pos : 0 < 36 * (r * (1 + r) / (1 - r) ^ 3) ^ 3 := by
      positivity
    rw [div_le_iff₀ hden_pos]
    field_simp [hu_pos.ne', hrpos.ne']
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r),
      show 0 ≤ r ^ 3 by positivity]
  have hcoef :
      ‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖
        ≤ 10 * Real.sqrt u := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (Real.sqrt_nonneg _))).mp hcoef_sq
  calc
    ‖fragPermScaledCubic r x‖
        = ‖(fragPermSaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold fragPermScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.sqrt u) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ = 10 * Real.sqrt (1 - r) * |x| ^ 3 := by dsimp [u]

private lemma fragPermScaledQuartic_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermScaledQuartic r x‖ ≤ 10 * (1 - r) * |x| ^ 4 := by
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hbpos : 0 < fragPermSaddleBReal r := fragPermSaddleBReal_pos_of_Ioo_half_one hr
  have hb4_nonneg : 0 ≤ fragPermSaddleB4Real r := by
    unfold fragPermSaddleB4Real
    positivity
  have hcoef :
      ‖(fragPermSaddleB4Real r : ℂ) /
          (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖ ≤ 10 * (1 - r) := by
    calc
      ‖(fragPermSaddleB4Real r : ℂ) /
          (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖
          = fragPermSaddleB4Real r / (24 * (fragPermSaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hbpos]
      _ ≤ 10 * (1 - r) := by
            unfold fragPermSaddleBReal fragPermSaddleB4Real
            have hden_pos : 0 < 24 * (r * (1 + r) / (1 - r) ^ 3) ^ 2 := by
              positivity
            rw [div_le_iff₀ hden_pos]
            field_simp [hu_pos.ne', hrpos.ne']
            nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r),
              show 0 ≤ r ^ 3 by positivity]
  calc
    ‖fragPermScaledQuartic r x‖
        = ‖(fragPermSaddleB4Real r : ℂ) /
            (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖ * |x| ^ 4 := by
          unfold fragPermScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (10 * (1 - r)) * |x| ^ 4 :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
      _ = 10 * (1 - r) * |x| ^ 4 := by ring

private lemma complex_norm_add_three_le (a b c : ℂ) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc
    ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ :=
      by
        simpa [add_comm, add_assoc, add_left_comm] using
          add_le_add_right (norm_add_le a b) ‖c‖
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring

private lemma fragPermLocalTaylorConst_pos : 0 < fragPermLocalTaylorConst := by
  unfold fragPermLocalTaylorConst
  positivity

private lemma fragPermLocalExponent_fifth_remainder_norm_le {r θ : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |θ| ≤ fragPermSaddleDeltaReal r)
    (hδle : fragPermSaddleDeltaReal r ≤ 1)
    (hδu : fragPermSaddleDeltaReal r ≤ (1 - r) / 4) :
    ‖fragPermLocalExponent r θ -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4)‖
      ≤ fragPermLocalTaylorConst * |θ| ^ 5 / (1 - r) ^ 6 := by
  let y : ℝ := |θ|
  let uR : ℝ := 1 - r
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  let geom : ℂ := (r : ℂ) * q / u
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let D : ℂ := (r : ℂ) ^ 3 / u ^ 4
  let P : ℂ :=
    -Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
      ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hr0 : 0 ≤ r := hrpos.le
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < uR := by dsimp [uR]; linarith [hr.2]
  have hu_nonneg : 0 ≤ uR := hu_pos.le
  have hu_le_one : uR ≤ 1 := by dsimp [uR]; linarith [hr.1]
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have huR_ne : uR ≠ 0 := hu_pos.ne'
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg θ
  have hy1 : y ≤ 1 := by
    dsimp [y]
    exact hθδ.trans hδle
  have hE2_ge_one : 1 ≤ Real.exp 2 := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hE1_le_E2 : Real.exp 1 ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)
  have hr_norm : ‖(r : ℂ)‖ = r :=
    (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
  have hu_norm : ‖u‖ = uR := by
    dsimp [u, uR]
    have hcoerce : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hcoerce]
    exact (RCLike.norm_ofReal (K := ℂ) (1 - r)).trans (abs_of_pos hu_pos)
  have hw_norm : ‖w‖ = y := by
    dsimp [w, y]
    simp
  have hθone : |θ| ≤ 1 := by simpa [y] using hy1
  have hq_norm : ‖q‖ ≤ 2 * y := by
    simpa [q, w, y] using fragPerm_exp_i_sub_one_norm_le_two_abs hθone
  have hq_minus_w : ‖q - w‖ ≤ y ^ 2 := by
    have hbase := fragPerm_exp_i_sub_one_sub_id_norm_le_sq hθone
    calc
      ‖q - w‖ = ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ := by
        dsimp [q, w]
      _ ≤ |θ| ^ 2 := hbase
      _ = y ^ 2 := by dsimp [y]
  have hη_norm : ‖q - w - w ^ 2 / 2‖ ≤ Real.exp 2 * y ^ 3 := by
    have hrest : q - w - w ^ 2 / 2 = ExpStirling.expLocalRemainder θ := by
      dsimp [q, w]
      rw [ExpStirling.expLocalRemainder_eq θ]
      ring_nf
      norm_num [Complex.ofReal_mul]
      ring
    rw [hrest]
    have hrem := ExpStirling.expLocalRemainder_norm_le_exp_one θ hθone
    calc
      ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 1 * |θ| ^ 3 := hrem
      _ ≤ Real.exp 2 * y ^ 3 := by
        dsimp [y]
        exact mul_le_mul_of_nonneg_right hE1_le_E2 (pow_nonneg (abs_nonneg θ) 3)
  have hfourth_norm :
      ‖q - w - w ^ 2 / 2 - w ^ 3 / 6‖ ≤ 2 * Real.exp 2 * y ^ 4 := by
    let t : ℂ := expLocalRemainderFifth θ
    let s4 : ℂ := w ^ 4 / 24
    have hrest : q - w - w ^ 2 / 2 - w ^ 3 / 6 = s4 + t := by
      dsimp [q, w, s4, t, expLocalRemainderFifth]
      rw [ExpStirling.expLocalRemainder_eq θ]
      ring_nf
      norm_num [Complex.ofReal_mul]
      ring
    have hs4 : ‖s4‖ ≤ y ^ 4 := by
      dsimp [s4]
      calc
        ‖w ^ 4 / 24‖ = y ^ 4 / 24 := by
          rw [norm_div, norm_pow, hw_norm, Complex.norm_ofNat]
        _ ≤ y ^ 4 := by nlinarith [pow_nonneg hy0 4]
    have ht : ‖t‖ ≤ Real.exp 2 * y ^ 4 := by
      have hrem := expLocalRemainderFifth_norm_le
        (by linarith [hy1] : |θ| ≤ 2)
      dsimp [t, y] at hrem ⊢
      calc
        ‖expLocalRemainderFifth θ‖ ≤ Real.exp 2 * |θ| ^ 5 := hrem
        _ ≤ Real.exp 2 * |θ| ^ 4 := by
          have h5_le_4 : |θ| ^ 5 ≤ |θ| ^ 4 := by
            calc
              |θ| ^ 5 = |θ| ^ 4 * |θ| := by ring
              _ ≤ |θ| ^ 4 * 1 :=
                mul_le_mul_of_nonneg_left hθone (pow_nonneg (abs_nonneg θ) 4)
              _ = |θ| ^ 4 := by ring
          exact mul_le_mul_of_nonneg_left h5_le_4 (Real.exp_pos 2).le
    rw [hrest]
    calc
      ‖s4 + t‖ ≤ ‖s4‖ + ‖t‖ := norm_add_le _ _
      _ ≤ y ^ 4 + Real.exp 2 * y ^ 4 := add_le_add hs4 ht
      _ ≤ 2 * Real.exp 2 * y ^ 4 := by
        have hleft : y ^ 4 ≤ Real.exp 2 * y ^ 4 := by
          calc
            y ^ 4 = 1 * y ^ 4 := by ring
            _ ≤ Real.exp 2 * y ^ 4 :=
              mul_le_mul_of_nonneg_right hE2_ge_one (pow_nonneg hy0 4)
        linarith
  have hgeom_norm : ‖geom‖ ≤ (1 / 2 : ℝ) := by
    have hnorm_eq : ‖geom‖ = r * ‖q‖ / uR := by
      dsimp [geom, u, uR]
      rw [norm_div, norm_mul, hr_norm, hu_norm]
    calc
      ‖geom‖ = r * ‖q‖ / uR := hnorm_eq
      _ ≤ r * (2 * y) / uR := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq_norm hr0) hu_nonneg
      _ ≤ 1 * (2 * fragPermSaddleDeltaReal r) / uR := by
        have hyδ : y ≤ fragPermSaddleDeltaReal r := by simpa [y] using hθδ
        exact div_le_div_of_nonneg_right
          (mul_le_mul (by linarith [hrle]) (mul_le_mul_of_nonneg_left hyδ (by norm_num))
            (mul_nonneg (by norm_num) hy0) zero_le_one) hu_nonneg
      _ ≤ 1 / 2 := by
        rw [one_mul]
        have hδu' : 2 * fragPermSaddleDeltaReal r ≤ uR / 2 := by
          have hδu0 : fragPermSaddleDeltaReal r ≤ uR / 4 := by
            simpa [uR] using hδu
          linarith
        rw [div_le_iff₀ hu_pos]
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hδu'
  have hgeom_ne : (1 : ℂ) - geom ≠ 0 := by
    intro hzero
    have hgeom_eq : geom = 1 := by exact sub_eq_zero.mp hzero |>.symm
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [hgeom_eq] using hgeom_norm
    norm_num at this
  have hinv_geom_norm : ‖(1 - geom)⁻¹‖ ≤ 2 := by
    have hdist : (1 / 2 : ℝ) ≤ ‖1 - geom‖ := by
      calc
        (1 / 2 : ℝ) ≤ 1 - ‖geom‖ := by linarith [hgeom_norm]
        _ ≤ ‖(1 : ℂ) - geom‖ := by
          have h := norm_sub_norm_le (1 : ℂ) geom
          have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by norm_num
          rw [hone] at h
          linarith
    rw [norm_inv]
    have hnorm_pos : 0 < ‖(1 : ℂ) - geom‖ := norm_pos_iff.mpr hgeom_ne
    rw [inv_le_comm₀ hnorm_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hdist]
  have hdecomp := fragPermLocalExponent_decomp (r := r) (θ := θ) hr.2 hgeom_ne
  dsimp [u, w, q, geom] at hdecomp
  have hP_decomp :
      P =
        A * (w ^ 3 / 6 + w ^ 4 / 24) +
          B * (w ^ 3 + (7 / 12 : ℂ) * w ^ 4) +
            D * (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4) := by
    have huc : u ≠ 0 := hu_ne
    have hw3 : w ^ 3 = -Complex.I * (θ : ℂ) ^ 3 := by
      dsimp [w]
      rw [mul_pow, Complex.I_pow_three]
      ring
    have hw4 : w ^ 4 = (θ : ℂ) ^ 4 := by
      dsimp [w]
      rw [mul_pow, Complex.I_pow_four]
      ring
    have hu_eq : u = (uR : ℂ) := by
      dsimp [u, uR]
      norm_num
    have hb3idR :
        fragPermSaddleB3Real r / 6 =
          r / (6 * uR ^ 2) + r ^ 2 / uR ^ 3 + r ^ 3 / uR ^ 4 := by
      dsimp [fragPermSaddleB3Real, uR]
      field_simp [huR_ne]
      ring
    have hb4idR :
        fragPermSaddleB4Real r / 24 =
          r / (24 * uR ^ 2) + 7 * r ^ 2 / (12 * uR ^ 3) +
            3 * r ^ 3 / (2 * uR ^ 4) + r ^ 4 / uR ^ 5 := by
      dsimp [fragPermSaddleB4Real, uR]
      field_simp [huR_ne]
      ring
    have hb3id :
        ((fragPermSaddleB3Real r : ℂ) / 6) =
          (r : ℂ) / (6 * u ^ 2) + (r : ℂ) ^ 2 / u ^ 3 +
            (r : ℂ) ^ 3 / u ^ 4 := by
      rw [hu_eq]
      have hcast : (((fragPermSaddleB3Real r / 6 : ℝ) : ℂ)) =
          ((r / (6 * uR ^ 2) + r ^ 2 / uR ^ 3 + r ^ 3 / uR ^ 4 : ℝ) : ℂ) := by
        exact_mod_cast hb3idR
      norm_num [Complex.ofReal_div] at hcast ⊢
      exact hcast
    have hb4id :
        ((fragPermSaddleB4Real r : ℂ) / 24) =
          (r : ℂ) / (24 * u ^ 2) + (7 * (r : ℂ) ^ 2) / (12 * u ^ 3) +
            (3 * (r : ℂ) ^ 3) / (2 * u ^ 4) + (r : ℂ) ^ 4 / u ^ 5 := by
      rw [hu_eq]
      have hcast : (((fragPermSaddleB4Real r / 24 : ℝ) : ℂ)) =
          ((r / (24 * uR ^ 2) + 7 * r ^ 2 / (12 * uR ^ 3) +
            3 * r ^ 3 / (2 * uR ^ 4) + r ^ 4 / uR ^ 5 : ℝ) : ℂ) := by
        exact_mod_cast hb4idR
      norm_num [Complex.ofReal_div] at hcast ⊢
      exact hcast
    dsimp [P, A, B, D]
    rw [hw3, hw4, hb3id, hb4id]
    ring_nf
  have hdiff :
      fragPermLocalExponent r θ - P =
        A * (ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24)) +
          B * ((q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4)) +
            D * (q ^ 3 * (1 - geom)⁻¹ -
              (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4)) := by
    rw [hdecomp, hP_decomp]
    dsimp [A, B, D]
    ring
  have hA_norm : ‖A‖ = r / uR ^ 2 := by
    dsimp [A, u, uR]
    rw [norm_div, norm_pow, hr_norm, hu_norm]
  have hB_norm : ‖B‖ = r ^ 2 / uR ^ 3 := by
    dsimp [B, u, uR]
    rw [norm_div, norm_pow, norm_pow, hr_norm, hu_norm]
  have hD_norm : ‖D‖ = r ^ 3 / uR ^ 4 := by
    dsimp [D, u, uR]
    rw [norm_div, norm_pow, norm_pow, hr_norm, hu_norm]
  have hden6_pos : 0 < uR ^ 6 := by positivity
  have hu2_ge_u6 : uR ^ 6 ≤ uR ^ 2 := by
    have hu4_le_one : uR ^ 4 ≤ 1 := by
      calc
        uR ^ 4 = (uR ^ 2) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by
          have hu2_le_one : uR ^ 2 ≤ 1 := by nlinarith [hu_nonneg, hu_le_one]
          exact pow_le_pow_left₀ (sq_nonneg uR) hu2_le_one 2
        _ = 1 := by norm_num
    calc
      uR ^ 6 = uR ^ 2 * uR ^ 4 := by ring
      _ ≤ uR ^ 2 * 1 := mul_le_mul_of_nonneg_left hu4_le_one (sq_nonneg uR)
      _ = uR ^ 2 := by ring
  have hu3_ge_u6 : uR ^ 6 ≤ uR ^ 3 := by
    have hu3_le_one : uR ^ 3 ≤ 1 := by
      calc
        uR ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hu_nonneg hu_le_one 3
        _ = 1 := by norm_num
    calc
      uR ^ 6 = uR ^ 3 * uR ^ 3 := by ring
      _ ≤ uR ^ 3 * 1 := mul_le_mul_of_nonneg_left hu3_le_one (by positivity)
      _ = uR ^ 3 := by ring
  have htermA :
      ‖A * (ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24))‖ ≤
        Real.exp 2 * y ^ 5 / uR ^ 6 := by
    have hrem : ‖ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24)‖ ≤
        Real.exp 2 * y ^ 5 := by
      have hrem5 := expLocalRemainderFifth_norm_le
        (by linarith [hy1] : |θ| ≤ 2)
      simpa [expLocalRemainderFifth, w, y] using hrem5
    calc
      ‖A * (ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24))‖
          = ‖A‖ *
            ‖ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24)‖ := by
            rw [norm_mul]
      _ ≤ (r / uR ^ 2) * (Real.exp 2 * y ^ 5) :=
          mul_le_mul hA_norm.le hrem (norm_nonneg _) (by positivity)
      _ ≤ Real.exp 2 * y ^ 5 / uR ^ 2 := by
        have hrle1 : r ≤ 1 := hrle
        field_simp [huR_ne]
        nlinarith [hrle1, Real.exp_pos 2, pow_nonneg hy0 5]
      _ ≤ Real.exp 2 * y ^ 5 / uR ^ 6 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (Real.exp_pos 2).le (pow_nonneg hy0 5)) hden6_pos hu2_ge_u6
  have hR2 :
      ‖(q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4)‖ ≤
        10 * Real.exp 2 * y ^ 5 := by
    have hR2_eq :
        (q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4) =
          2 * w * (q - w - w ^ 2 / 2 - w ^ 3 / 6) +
            ((q - w) ^ 2 - (w ^ 2 / 2) ^ 2) := by
      ring
    rw [hR2_eq]
    have hsum2 : ‖q - w + w ^ 2 / 2‖ ≤ 2 * y ^ 2 := by
      calc
        ‖q - w + w ^ 2 / 2‖ ≤ ‖q - w‖ + ‖w ^ 2 / 2‖ := norm_add_le _ _
        _ ≤ y ^ 2 + y ^ 2 := by
          have hs2 : ‖w ^ 2 / 2‖ ≤ y ^ 2 := by
            calc
              ‖w ^ 2 / 2‖ = y ^ 2 / 2 := by
                rw [norm_div, norm_pow, hw_norm, Complex.norm_ofNat]
              _ ≤ y ^ 2 := by nlinarith [pow_nonneg hy0 2]
          exact add_le_add hq_minus_w hs2
        _ = 2 * y ^ 2 := by ring
    have hsquare :
        ‖(q - w) ^ 2 - (w ^ 2 / 2) ^ 2‖ ≤ 2 * Real.exp 2 * y ^ 5 := by
      have hsq_eq :
          (q - w) ^ 2 - (w ^ 2 / 2) ^ 2 =
            (q - w - w ^ 2 / 2) * (q - w + w ^ 2 / 2) := by ring
      rw [hsq_eq, norm_mul]
      calc
        ‖q - w - w ^ 2 / 2‖ * ‖q - w + w ^ 2 / 2‖
            ≤ (Real.exp 2 * y ^ 3) * (2 * y ^ 2) :=
              mul_le_mul hη_norm hsum2 (norm_nonneg _) (by positivity)
        _ = 2 * Real.exp 2 * y ^ 5 := by ring
    calc
      ‖2 * w * (q - w - w ^ 2 / 2 - w ^ 3 / 6) +
          ((q - w) ^ 2 - (w ^ 2 / 2) ^ 2)‖
          ≤ ‖2 * w * (q - w - w ^ 2 / 2 - w ^ 3 / 6)‖ +
              ‖(q - w) ^ 2 - (w ^ 2 / 2) ^ 2‖ := norm_add_le _ _
      _ ≤ (2 * y) * (2 * Real.exp 2 * y ^ 4) +
            2 * Real.exp 2 * y ^ 5 := by
          exact add_le_add
            (by
              rw [norm_mul, norm_mul, Complex.norm_ofNat, hw_norm]
              exact mul_le_mul_of_nonneg_left hfourth_norm (by positivity))
            hsquare
      _ ≤ 10 * Real.exp 2 * y ^ 5 := by
        have hnon : 0 ≤ Real.exp 2 * y ^ 5 := by positivity
        nlinarith
  have htermB :
      ‖B * ((q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4))‖ ≤
        10 * Real.exp 2 * y ^ 5 / uR ^ 6 := by
    calc
      ‖B * ((q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4))‖
          = ‖B‖ * ‖(q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4)‖ := by
            rw [norm_mul]
      _ ≤ (r ^ 2 / uR ^ 3) * (10 * Real.exp 2 * y ^ 5) :=
          mul_le_mul hB_norm.le hR2 (norm_nonneg _) (by positivity)
      _ ≤ 10 * Real.exp 2 * y ^ 5 / uR ^ 3 := by
        have hr2le : r ^ 2 ≤ 1 := by nlinarith [hr0, hrle]
        field_simp [huR_ne]
        nlinarith [hr2le, Real.exp_pos 2, pow_nonneg hy0 5]
      _ ≤ 10 * Real.exp 2 * y ^ 5 / uR ^ 6 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 2).le) (pow_nonneg hy0 5))
          hden6_pos hu3_ge_u6
  have hR3a :
      ‖q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4)‖ ≤
        20 * Real.exp 2 * y ^ 5 := by
    have hcube_eq :
        q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4) =
          3 * w ^ 2 * (q - w - w ^ 2 / 2) +
            3 * w * (q - w) ^ 2 + (q - w) ^ 3 := by
      ring
    rw [hcube_eq]
    calc
      ‖3 * w ^ 2 * (q - w - w ^ 2 / 2) +
          3 * w * (q - w) ^ 2 + (q - w) ^ 3‖
          ≤ ‖3 * w ^ 2 * (q - w - w ^ 2 / 2)‖ +
              ‖3 * w * (q - w) ^ 2‖ + ‖(q - w) ^ 3‖ := by
            calc
              ‖3 * w ^ 2 * (q - w - w ^ 2 / 2) +
                  3 * w * (q - w) ^ 2 + (q - w) ^ 3‖
                  ≤ ‖3 * w ^ 2 * (q - w - w ^ 2 / 2) +
                      3 * w * (q - w) ^ 2‖ + ‖(q - w) ^ 3‖ :=
                    norm_add_le _ _
              _ ≤ (‖3 * w ^ 2 * (q - w - w ^ 2 / 2)‖ +
                    ‖3 * w * (q - w) ^ 2‖) + ‖(q - w) ^ 3‖ :=
                    add_le_add (norm_add_le _ _) (le_refl _)
              _ = ‖3 * w ^ 2 * (q - w - w ^ 2 / 2)‖ +
                    ‖3 * w * (q - w) ^ 2‖ + ‖(q - w) ^ 3‖ := by ring
      _ ≤ 3 * y ^ 2 * (Real.exp 2 * y ^ 3) +
            3 * y * (y ^ 2) ^ 2 + (y ^ 2) ^ 3 := by
          have ht1 :
              ‖3 * w ^ 2 * (q - w - w ^ 2 / 2)‖ ≤
                3 * y ^ 2 * (Real.exp 2 * y ^ 3) := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow, hw_norm]
            exact mul_le_mul_of_nonneg_left hη_norm (by positivity)
          have ht2 :
              ‖3 * w * (q - w) ^ 2‖ ≤ 3 * y * (y ^ 2) ^ 2 := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat, hw_norm, norm_pow]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hq_minus_w 2) (by positivity)
          have ht3 : ‖(q - w) ^ 3‖ ≤ (y ^ 2) ^ 3 := by
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) hq_minus_w 3
          exact add_le_add (add_le_add ht1 ht2) ht3
      _ ≤ 20 * Real.exp 2 * y ^ 5 := by
        have hy6_le_y5 : y ^ 6 ≤ y ^ 5 := by
          calc
            y ^ 6 = y ^ 5 * y := by ring
            _ ≤ y ^ 5 * 1 := mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy0 5)
            _ = y ^ 5 := by ring
        have hplain : 3 * y ^ 5 ≤ 3 * Real.exp 2 * y ^ 5 := by
          calc
            3 * y ^ 5 = (3 * 1) * y ^ 5 := by ring
            _ ≤ (3 * Real.exp 2) * y ^ 5 :=
              mul_le_mul_of_nonneg_right (by nlinarith [hE2_ge_one])
                (pow_nonneg hy0 5)
            _ = 3 * Real.exp 2 * y ^ 5 := by ring
        have hy6_exp : y ^ 6 ≤ Real.exp 2 * y ^ 5 := by
          calc
            y ^ 6 ≤ y ^ 5 := hy6_le_y5
            _ = 1 * y ^ 5 := by ring
            _ ≤ Real.exp 2 * y ^ 5 :=
              mul_le_mul_of_nonneg_right hE2_ge_one (pow_nonneg hy0 5)
        calc
          3 * y ^ 2 * (Real.exp 2 * y ^ 3) +
              3 * y * (y ^ 2) ^ 2 + (y ^ 2) ^ 3
              = 3 * Real.exp 2 * y ^ 5 + 3 * y ^ 5 + y ^ 6 := by ring
          _ ≤ 3 * Real.exp 2 * y ^ 5 + 3 * Real.exp 2 * y ^ 5 +
                Real.exp 2 * y ^ 5 := by
            exact add_le_add (add_le_add (le_refl _) hplain) hy6_exp
          _ ≤ 20 * Real.exp 2 * y ^ 5 := by
            have hnon : 0 ≤ Real.exp 2 * y ^ 5 := by positivity
            nlinarith
  have hq4_diff :
      ‖q ^ 4 - w ^ 4‖ ≤ 20 * y ^ 5 := by
    have hfac : q ^ 4 - w ^ 4 =
        (q - w) * (q ^ 3 + q ^ 2 * w + q * w ^ 2 + w ^ 3) := by ring
    rw [hfac, norm_mul]
    have hsum :
        ‖q ^ 3 + q ^ 2 * w + q * w ^ 2 + w ^ 3‖ ≤ 20 * y ^ 3 := by
      calc
        ‖q ^ 3 + q ^ 2 * w + q * w ^ 2 + w ^ 3‖
            ≤ ‖q ^ 3‖ + ‖q ^ 2 * w‖ + ‖q * w ^ 2‖ + ‖w ^ 3‖ := by
              calc
                ‖q ^ 3 + q ^ 2 * w + q * w ^ 2 + w ^ 3‖
                    ≤ ‖q ^ 3 + q ^ 2 * w + q * w ^ 2‖ + ‖w ^ 3‖ :=
                      norm_add_le _ _
                _ ≤ (‖q ^ 3 + q ^ 2 * w‖ + ‖q * w ^ 2‖) + ‖w ^ 3‖ :=
                      add_le_add (norm_add_le _ _) (le_refl _)
                _ ≤ ((‖q ^ 3‖ + ‖q ^ 2 * w‖) + ‖q * w ^ 2‖) + ‖w ^ 3‖ :=
                      add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
                _ = ‖q ^ 3‖ + ‖q ^ 2 * w‖ + ‖q * w ^ 2‖ + ‖w ^ 3‖ := by ring
        _ = ‖q‖ ^ 3 + ‖q‖ ^ 2 * ‖w‖ + ‖q‖ * ‖w‖ ^ 2 + ‖w‖ ^ 3 := by
          simp [norm_pow]
        _ ≤ (2 * y) ^ 3 + (2 * y) ^ 2 * y + (2 * y) * y ^ 2 + y ^ 3 := by
          have hw_le : ‖w‖ ≤ y := by rw [hw_norm]
          have hq2 := pow_le_pow_left₀ (norm_nonneg q) hq_norm 2
          have hq3 := pow_le_pow_left₀ (norm_nonneg q) hq_norm 3
          have hw2 := pow_le_pow_left₀ (norm_nonneg w) hw_le 2
          have hw3 := pow_le_pow_left₀ (norm_nonneg w) hw_le 3
          exact add_le_add (add_le_add (add_le_add hq3
            (mul_le_mul hq2 hw_le (norm_nonneg _) (by positivity)))
            (mul_le_mul hq_norm hw2 (by positivity) (by positivity))) hw3
        _ ≤ 20 * y ^ 3 := by
          calc
            (2 * y) ^ 3 + (2 * y) ^ 2 * y + (2 * y) * y ^ 2 + y ^ 3
                = 15 * y ^ 3 := by ring
            _ ≤ 20 * y ^ 3 := by
              exact mul_le_mul_of_nonneg_right (by norm_num : (15 : ℝ) ≤ 20)
                (pow_nonneg hy0 3)
    calc
      ‖q - w‖ * ‖q ^ 3 + q ^ 2 * w + q * w ^ 2 + w ^ 3‖
          ≤ y ^ 2 * (20 * y ^ 3) :=
            mul_le_mul hq_minus_w hsum (norm_nonneg _) (by positivity)
      _ = 20 * y ^ 5 := by ring
  have hgeom_tail :
      ‖q ^ 4 * (1 - geom)⁻¹ - w ^ 4‖ ≤ 50 * y ^ 5 / uR := by
    have hsplit :
        q ^ 4 * (1 - geom)⁻¹ - w ^ 4 =
          (q ^ 4 - w ^ 4) * (1 - geom)⁻¹ +
            w ^ 4 * (geom * (1 - geom)⁻¹) := by
      field_simp [hgeom_ne]
      ring
    rw [hsplit]
    have hgeom_small : ‖geom‖ ≤ 2 * y / uR := by
      calc
        ‖geom‖ = r * ‖q‖ / uR := by
          dsimp [geom, u, uR]
          rw [norm_div, norm_mul, hr_norm, hu_norm]
        _ ≤ r * (2 * y) / uR := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hq_norm hr0) hu_nonneg
        _ ≤ 1 * (2 * y) / uR := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hrle (by positivity)) hu_nonneg
        _ = 2 * y / uR := by ring
    have hsecond :
        ‖w ^ 4 * (geom * (1 - geom)⁻¹)‖ ≤ 4 * y ^ 5 / uR := by
      rw [norm_mul, norm_mul, norm_pow, hw_norm]
      calc
        y ^ 4 * (‖geom‖ * ‖(1 - geom)⁻¹‖)
            ≤ y ^ 4 * ((2 * y / uR) * 2) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hgeom_small hinv_geom_norm (norm_nonneg _) (by positivity))
                (pow_nonneg hy0 4)
        _ = 4 * y ^ 5 / uR := by ring
    calc
      ‖(q ^ 4 - w ^ 4) * (1 - geom)⁻¹ +
          w ^ 4 * (geom * (1 - geom)⁻¹)‖
          ≤ ‖(q ^ 4 - w ^ 4) * (1 - geom)⁻¹‖ +
              ‖w ^ 4 * (geom * (1 - geom)⁻¹)‖ :=
            norm_add_le _ _
      _ ≤ 40 * y ^ 5 + 4 * y ^ 5 / uR := by
        have hfirst :
            ‖(q ^ 4 - w ^ 4) * (1 - geom)⁻¹‖ ≤ 40 * y ^ 5 := by
          rw [norm_mul]
          calc
            ‖q ^ 4 - w ^ 4‖ * ‖(1 - geom)⁻¹‖
                ≤ (20 * y ^ 5) * 2 :=
                  mul_le_mul hq4_diff hinv_geom_norm (norm_nonneg _) (by positivity)
            _ = 40 * y ^ 5 := by ring
        exact add_le_add hfirst hsecond
      _ ≤ 50 * y ^ 5 / uR := by
        have hy5_nonneg : 0 ≤ y ^ 5 := pow_nonneg hy0 5
        have h40 : 40 * y ^ 5 ≤ 40 * y ^ 5 / uR := by
          rw [le_div_iff₀ hu_pos]
          nlinarith [hu_le_one, hy5_nonneg]
        calc
          40 * y ^ 5 + 4 * y ^ 5 / uR
              ≤ 40 * y ^ 5 / uR + 4 * y ^ 5 / uR := by nlinarith [h40]
          _ = 44 * y ^ 5 / uR := by ring
          _ ≤ 50 * y ^ 5 / uR := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by norm_num : (44 : ℝ) ≤ 50) hy5_nonneg)
              hu_nonneg
  have hR3 :
      ‖q ^ 3 * (1 - geom)⁻¹ -
          (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4)‖ ≤
        100 * Real.exp 2 * y ^ 5 / uR ^ 2 := by
    have hsplit :
        q ^ 3 * (1 - geom)⁻¹ -
            (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4) =
          (q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4)) +
            ((r : ℂ) / u) * (q ^ 4 * (1 - geom)⁻¹ - w ^ 4) := by
      have hgeom_decomp :
          q ^ 3 * (1 - geom)⁻¹ =
            q ^ 3 + ((r : ℂ) / u) * (q ^ 4 * (1 - geom)⁻¹) := by
        have hinv_sub : (1 - geom)⁻¹ - 1 = geom * (1 - geom)⁻¹ := by
          field_simp [hgeom_ne]
          ring
        calc
          q ^ 3 * (1 - geom)⁻¹
              = q ^ 3 + q ^ 3 * ((1 - geom)⁻¹ - 1) := by ring
          _ = q ^ 3 + q ^ 3 * (geom * (1 - geom)⁻¹) := by rw [hinv_sub]
          _ = q ^ 3 + ((r : ℂ) / u) * (q ^ 4 * (1 - geom)⁻¹) := by
            dsimp [geom]
            field_simp [hu_ne]
      rw [hgeom_decomp]
      ring
    rw [hsplit]
    have hcoef_ru : ‖(r : ℂ) / u‖ ≤ 1 / uR := by
      rw [norm_div, hr_norm, hu_norm]
      exact div_le_div_of_nonneg_right hrle hu_nonneg
    have hsecond :
        ‖((r : ℂ) / u) * (q ^ 4 * (1 - geom)⁻¹ - w ^ 4)‖ ≤
          50 * y ^ 5 / uR ^ 2 := by
      rw [norm_mul]
      calc
        ‖(r : ℂ) / u‖ * ‖q ^ 4 * (1 - geom)⁻¹ - w ^ 4‖
            ≤ (1 / uR) * (50 * y ^ 5 / uR) :=
              mul_le_mul hcoef_ru hgeom_tail (norm_nonneg _) (by positivity)
        _ = 50 * y ^ 5 / uR ^ 2 := by field_simp [huR_ne]
    calc
      ‖(q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4)) +
          ((r : ℂ) / u) * (q ^ 4 * (1 - geom)⁻¹ - w ^ 4)‖
          ≤ ‖q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4)‖ +
              ‖((r : ℂ) / u) * (q ^ 4 * (1 - geom)⁻¹ - w ^ 4)‖ :=
            norm_add_le _ _
      _ ≤ 20 * Real.exp 2 * y ^ 5 + 50 * y ^ 5 / uR ^ 2 :=
            add_le_add hR3a hsecond
      _ ≤ 100 * Real.exp 2 * y ^ 5 / uR ^ 2 := by
        have hy5_nonneg : 0 ≤ y ^ 5 := pow_nonneg hy0 5
        have hu2_pos : 0 < uR ^ 2 := by positivity
        have hu2_le_one : uR ^ 2 ≤ 1 := by
          calc
            uR ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hu_nonneg hu_le_one 2
            _ = 1 := by norm_num
        have h20 :
            20 * Real.exp 2 * y ^ 5 ≤ 20 * Real.exp 2 * y ^ 5 / uR ^ 2 := by
          simpa using
            div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 2).le) hy5_nonneg)
              hu2_pos hu2_le_one
        have h50 :
            50 * y ^ 5 / uR ^ 2 ≤ 50 * Real.exp 2 * y ^ 5 / uR ^ 2 := by
          have hcoef50 : (50 : ℝ) ≤ 50 * Real.exp 2 := by
            calc
              (50 : ℝ) = 50 * 1 := by norm_num
              _ ≤ 50 * Real.exp 2 :=
                mul_le_mul_of_nonneg_left hE2_ge_one (by norm_num)
          have hnum50 : 50 * y ^ 5 ≤ 50 * Real.exp 2 * y ^ 5 := by
            exact mul_le_mul_of_nonneg_right hcoef50 hy5_nonneg
          exact div_le_div_of_nonneg_right
            (by simpa [mul_assoc] using hnum50)
            hu2_pos.le
        calc
          20 * Real.exp 2 * y ^ 5 + 50 * y ^ 5 / uR ^ 2
              ≤ 20 * Real.exp 2 * y ^ 5 / uR ^ 2 +
                  50 * Real.exp 2 * y ^ 5 / uR ^ 2 := add_le_add h20 h50
          _ = 70 * Real.exp 2 * y ^ 5 / uR ^ 2 := by ring_nf
          _ ≤ 100 * Real.exp 2 * y ^ 5 / uR ^ 2 := by
            have hcoef70 :
                70 * Real.exp 2 ≤ 100 * Real.exp 2 :=
              mul_le_mul_of_nonneg_right (by norm_num : (70 : ℝ) ≤ 100)
                (Real.exp_pos 2).le
            have hnum70 :
                70 * Real.exp 2 * y ^ 5 ≤ 100 * Real.exp 2 * y ^ 5 := by
              exact mul_le_mul_of_nonneg_right hcoef70 hy5_nonneg
            exact div_le_div_of_nonneg_right
              (by simpa [mul_assoc] using hnum70)
              hu2_pos.le
  have htermD :
      ‖D * (q ^ 3 * (1 - geom)⁻¹ -
          (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4))‖ ≤
        100 * Real.exp 2 * y ^ 5 / uR ^ 6 := by
    calc
      ‖D * (q ^ 3 * (1 - geom)⁻¹ -
          (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4))‖
          = ‖D‖ * ‖q ^ 3 * (1 - geom)⁻¹ -
              (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4)‖ := by
            rw [norm_mul]
      _ ≤ (r ^ 3 / uR ^ 4) * (100 * Real.exp 2 * y ^ 5 / uR ^ 2) :=
          mul_le_mul hD_norm.le hR3 (norm_nonneg _) (by positivity)
      _ ≤ 100 * Real.exp 2 * y ^ 5 / uR ^ 6 := by
        have hr3le : r ^ 3 ≤ 1 := by
          have hr2le : r ^ 2 ≤ 1 := by
            calc
              r ^ 2 = 1 * (r * r) := by ring
              _ ≤ 1 * (1 * r) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hrle hr0) (by norm_num)
              _ ≤ 1 * (1 * 1) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hrle (by norm_num)) (by norm_num)
              _ = 1 := by ring
          calc
            r ^ 3 = r ^ 2 * r := by ring
            _ ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hrle (sq_nonneg r)
            _ = r ^ 2 := by ring
            _ ≤ 1 := hr2le
        have hCnon : 0 ≤ 100 * Real.exp 2 * y ^ 5 := by positivity
        have hu6_nonneg : 0 ≤ uR ^ 6 := pow_nonneg hu_nonneg 6
        calc
          (r ^ 3 / uR ^ 4) * (100 * Real.exp 2 * y ^ 5 / uR ^ 2)
              = r ^ 3 * (100 * Real.exp 2 * y ^ 5) / uR ^ 6 := by
                field_simp [huR_ne]
          _ ≤ 1 * (100 * Real.exp 2 * y ^ 5) / uR ^ 6 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hr3le hCnon) hu6_nonneg
          _ = 100 * Real.exp 2 * y ^ 5 / uR ^ 6 := by ring_nf
  rw [show fragPermLocalExponent r θ -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4) =
        fragPermLocalExponent r θ - P by rfl]
  rw [hdiff]
  calc
    ‖A * (ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24)) +
        B * ((q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4)) +
          D * (q ^ 3 * (1 - geom)⁻¹ -
            (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4))‖
        ≤ ‖A * (ExpStirling.expLocalRemainder θ - (w ^ 3 / 6 + w ^ 4 / 24))‖ +
            ‖B * ((q ^ 2 - w ^ 2) - (w ^ 3 + (7 / 12 : ℂ) * w ^ 4))‖ +
              ‖D * (q ^ 3 * (1 - geom)⁻¹ -
                (w ^ 3 + ((3 / 2 : ℂ) + (r : ℂ) / u) * w ^ 4))‖ :=
          complex_norm_add_three_le _ _ _
    _ ≤ Real.exp 2 * y ^ 5 / uR ^ 6 +
          10 * Real.exp 2 * y ^ 5 / uR ^ 6 +
            100 * Real.exp 2 * y ^ 5 / uR ^ 6 :=
        add_le_add (add_le_add htermA htermB) htermD
    _ ≤ fragPermLocalTaylorConst * |θ| ^ 5 / (1 - r) ^ 6 := by
      dsimp [fragPermLocalTaylorConst, y, uR]
      have hden_nonneg : 0 ≤ (1 - r) ^ 6 := by
        simpa [uR] using pow_nonneg hu_nonneg 6
      have hnon : 0 ≤ Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6 := by
        exact div_nonneg
          (mul_nonneg (Real.exp_pos 2).le (pow_nonneg (abs_nonneg θ) 5))
          hden_nonneg
      have hsum111 :
          Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6 +
              10 * Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6 +
                100 * Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6 =
            111 * (Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6) := by
        ring_nf
      rw [hsum111]
      calc
        111 * (Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6)
            ≤ 100000 * (Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6) := by
          exact mul_le_mul_of_nonneg_right (by norm_num : (111 : ℝ) ≤ 100000) hnon
        _ = 100000 * Real.exp 2 * |θ| ^ 5 / (1 - r) ^ 6 := by ring_nf

private lemma fragPermScaledRemainderConst_pos : 0 < fragPermScaledRemainderConst := by
  unfold fragPermScaledRemainderConst
  exact mul_pos (by norm_num : (0 : ℝ) < 1000) fragPermLocalTaylorConst_pos

private lemma fragPermScaledRemainder_eq_unscaled {r x : ℝ}
    (hb : 0 < fragPermSaddleBReal r) :
    fragPermScaledRemainder r x =
      fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4) := by
  have hsqrt_ne : (Real.sqrt (fragPermSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (fragPermSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_sq := fragPerm_sqrtB_sq hb
  have hsqrt_pow4 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 =
        (fragPermSaddleBReal r : ℂ) ^ 2 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 2 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
  have hθ3 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 =
        (x : ℂ) ^ 3 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3 := by
    norm_num [Complex.ofReal_div]
    ring
  have hθ4 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4 =
        (x : ℂ) ^ 4 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 := by
    norm_num [Complex.ofReal_div]
    ring
  unfold fragPermScaledRemainder fragPermScaledCubic fragPermScaledQuartic
  rw [hθ3, hθ4, hsqrt_pow4]
  field_simp [hsqrt_ne, hb_ne]
  ring

private lemma fragPermScaledRemainder_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r)
    (hδle : fragPermSaddleDeltaReal r ≤ 1)
    (hδu : fragPermSaddleDeltaReal r ≤ (1 - r) / 4) :
    ‖fragPermScaledRemainder r x‖ ≤
      fragPermScaledRemainderConst * ((1 - r) * Real.sqrt (1 - r)) * |x| ^ 5 := by
  let u : ℝ := 1 - r
  let D : ℝ := u * Real.sqrt u
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := fragPermSaddleBReal_pos_of_Ioo_half_one hr
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hrem := fragPermLocalExponent_fifth_remainder_norm_le
    (r := r) (θ := x / Real.sqrt (fragPermSaddleBReal r)) hr hθδ hδle hδu
  rw [fragPermScaledRemainder_eq_unscaled hbpos]
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hD_eq : D = u ^ (3 / 2 : ℝ) := by
    dsimp [D]
    rw [Real.sqrt_eq_rpow]
    calc
      u * u ^ (1 / 2 : ℝ) = u ^ (1 : ℝ) * u ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = u ^ ((1 : ℝ) + 1 / 2) := by
        rw [Real.rpow_add hu_pos]
      _ = u ^ (3 / 2 : ℝ) := by norm_num
  have hsqrt_lower :
      (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) ≤
        Real.sqrt (fragPermSaddleBReal r) := by
    simpa [u] using fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  have hlower_pos : 0 < (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) := by
    positivity
  have hupow_pos : 0 < u ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hu_pos _
  have hθ_abs_le :
      |x / Real.sqrt (fragPermSaddleBReal r)| ≤ 2 * D * |x| := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    calc
      |x| / Real.sqrt (fragPermSaddleBReal r) ≤
          |x| / ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) :=
            div_le_div_of_nonneg_left (abs_nonneg x) hlower_pos hsqrt_lower
      _ = 2 * D * |x| := by
        rw [hD_eq, Real.rpow_neg hu_nonneg (3 / 2 : ℝ)]
        field_simp [hupow_pos.ne']
  have hθ5_le :
      |x / Real.sqrt (fragPermSaddleBReal r)| ^ 5 ≤ (2 * D * |x|) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 5
  have hscale :
      (2 * D * |x|) ^ 5 / u ^ 6 = 32 * D * |x| ^ 5 := by
    have hDpow : D ^ 5 = D * u ^ 6 := by
      dsimp [D]
      rw [show (u * Real.sqrt u) ^ 5 =
          u ^ 5 * (Real.sqrt u) * ((Real.sqrt u) ^ 2) ^ 2 by ring]
      rw [Real.sq_sqrt hu_nonneg]
      ring
    calc
      (2 * D * |x|) ^ 5 / u ^ 6 =
          (32 * D ^ 5 * |x| ^ 5) / u ^ 6 := by ring
      _ = (32 * (D * u ^ 6) * |x| ^ 5) / u ^ 6 := by rw [hDpow]
      _ = 32 * D * |x| ^ 5 := by
        field_simp [hu_pos.ne']
  have hlocal_nonneg : 0 ≤ fragPermLocalTaylorConst := fragPermLocalTaylorConst_pos.le
  have hu6_nonneg : 0 ≤ u ^ 6 := pow_nonneg hu_nonneg 6
  calc
    ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4)‖
        ≤ fragPermLocalTaylorConst *
            |x / Real.sqrt (fragPermSaddleBReal r)| ^ 5 / (1 - r) ^ 6 := hrem
    _ ≤ fragPermLocalTaylorConst * (2 * D * |x|) ^ 5 / u ^ 6 := by
      dsimp [u]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ5_le hlocal_nonneg) hu6_nonneg
    _ = fragPermLocalTaylorConst * ((2 * D * |x|) ^ 5 / u ^ 6) := by ring
    _ = fragPermLocalTaylorConst * (32 * D * |x| ^ 5) := by
      rw [hscale]
    _ ≤ fragPermScaledRemainderConst * D * |x| ^ 5 := by
      unfold fragPermScaledRemainderConst
      have hcoef : fragPermLocalTaylorConst * 32 ≤ 1000 * fragPermLocalTaylorConst := by
        nlinarith [fragPermLocalTaylorConst_pos]
      have htail_nonneg : 0 ≤ D * |x| ^ 5 := by positivity
      calc
        fragPermLocalTaylorConst * (32 * D * |x| ^ 5) =
            (fragPermLocalTaylorConst * 32) * (D * |x| ^ 5) := by ring
        _ ≤ (1000 * fragPermLocalTaylorConst) * (D * |x| ^ 5) :=
          mul_le_mul_of_nonneg_right hcoef htail_nonneg
        _ = (1000 * fragPermLocalTaylorConst) * D * |x| ^ 5 := by ring
    _ = fragPermScaledRemainderConst * ((1 - r) * Real.sqrt (1 - r)) * |x| ^ 5 := by
      dsimp [D, u]

end FragmentedPermHAdmissible
end

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 800000
theorem solution {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r)
    (hδle : fragPermSaddleDeltaReal r ≤ 1)
    (hδu : fragPermSaddleDeltaReal r ≤ (1 - r) / 4)
    (hWnorm : ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖
      ≤ fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)) * fragPermGaussianDom x := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hu_le_one : u ≤ 1 := by dsimp [u]; linarith [hr.1]
  have hbpos : 0 < fragPermSaddleBReal r := fragPermSaddleBReal_pos_of_Ioo_half_one hr
  let C : ℂ := fragPermScaledCubic r x
  let Q : ℂ := fragPermScaledQuartic r x
  let R : ℂ := fragPermScaledRemainder r x
  let W : ℂ := fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))
  let y : ℝ := |x|
  let A : ℝ := Real.sqrt u
  let B : ℝ := u
  let D : ℝ := u * Real.sqrt u
  let K : ℝ := fragPermScaledRemainderConst
  let S : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
  let T : ℝ := (10 * y ^ 4 + K * y ^ 5) * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)
  let G : ℝ := y ^ 5 + y ^ 6 + y ^ 7 + y ^ 8 + y ^ 9 + y ^ 10 +
    y ^ 11 + y ^ 12 + y ^ 13 + y ^ 14 + y ^ 15
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact fragPermScaledRemainderConst_pos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg x
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; exact hu_nonneg
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hB_le_A : B ≤ A := by
    dsimp [A, B]
    exact Real.le_sqrt_of_sq_le (by nlinarith [hu_nonneg, hu_le_one])
  have hA_le_one : A ≤ 1 := by
    dsimp [A]
    simpa using Real.sqrt_le_sqrt hu_le_one
  have hD_le_A : D ≤ A := by
    dsimp [A, D]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg u) hu_le_one
  have hD_le_B : D ≤ B := by
    dsimp [B, D]
    exact mul_le_of_le_one_right hu_nonneg hA_le_one
  have hA_mul_B : A * B = D := by
    dsimp [A, B, D]
    ring
  have hA_cube : A ^ 3 = D := by
    dsimp [A, D]
    calc
      (Real.sqrt u) ^ 3 = Real.sqrt u * (Real.sqrt u) ^ 2 := by ring
      _ = Real.sqrt u * u := by rw [Real.sq_sqrt hu_nonneg]
      _ = u * Real.sqrt u := by ring
  have hWsplit : W = C + Q + R := by
    dsimp [W, C, Q, R]
    exact fragPermLocalExponent_scaled_split r x
  have hP :
      saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x =
        1 + C + Q + C ^ 2 / 2 := by
    dsimp [C, Q]
    exact fragPerm_saddleSecondPoly_eq_scaled_terms hbpos
  have herr := complex_exp_second_error_bound C Q R W hWsplit (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ 10 * A * y ^ 3 := by
    dsimp [C, A, y, u]
    simpa [mul_assoc] using fragPermScaledCubic_norm_le (r := r) (x := x) hr
  have hQ_B : ‖Q‖ ≤ 10 * B * y ^ 4 := by
    dsimp [Q, B, y, u]
    simpa [mul_assoc] using fragPermScaledQuartic_norm_le (r := r) (x := x) hr
  have hQ_A : ‖Q‖ ≤ 10 * A * y ^ 4 := by
    exact hQ_B.trans (by gcongr)
  have hR_D : ‖R‖ ≤ K * D * y ^ 5 := by
    dsimp [R, K, D, y, u]
    simpa [mul_assoc] using
      fragPermScaledRemainder_norm_le (r := r) (x := x) hr hθδ hδle hδu
  have hR_A : ‖R‖ ≤ K * A * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hR_B : ‖R‖ ≤ K * B * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hWpoly : ‖W‖ ≤ A * S := by
    calc
      ‖W‖ = ‖C + Q + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖R‖ := complex_norm_add_three_le _ _ _
      _ ≤ 10 * A * y ^ 3 + 10 * A * y ^ 4 + K * A * y ^ 5 :=
        add_le_add (add_le_add hC hQ_A) hR_A
      _ = A * S := by
        dsimp [S]
        ring
  have hWcube :
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * D * S ^ 3 := by
    calc
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * (A * S) ^ 3 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg W) hWpoly 3) (Real.exp_pos 1).le
      _ = Real.exp 1 * D * S ^ 3 := by
        rw [mul_pow, hA_cube]
        ring
  have hQR : ‖Q‖ + ‖R‖ ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
    calc
      ‖Q‖ + ‖R‖ ≤ 10 * B * y ^ 4 + K * B * y ^ 5 := add_le_add hQ_B hR_B
      _ = B * (10 * y ^ 4 + K * y ^ 5) := by ring
  have hCQR : 2 * ‖C‖ + ‖Q‖ + ‖R‖ ≤ A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by
    calc
      2 * ‖C‖ + ‖Q‖ + ‖R‖
          ≤ 2 * (10 * A * y ^ 3) + 10 * A * y ^ 4 + K * A * y ^ 5 := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hQ_A) hR_A
      _ = A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by ring
  have hprod :
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) ≤ D * T := by
    calc
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖)
          ≤ (B * (10 * y ^ 4 + K * y ^ 5)) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) := by
            have hupper_nonneg : 0 ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
              positivity
            exact mul_le_mul hQR hCQR (by positivity) hupper_nonneg
      _ = D * T := by
        dsimp [T]
        rw [show B * (10 * y ^ 4 + K * y ^ 5) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) =
              (A * B) * ((10 * y ^ 4 + K * y ^ 5) *
                (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) by ring]
        rw [hA_mul_B]
  have hpoly :
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T ≤ fragPermLocalL1Const * G := by
    have hK20_nonneg : 0 ≤ 20 + K := by positivity
    have hK10_nonneg : 0 ≤ 10 + K := by positivity
    have hK30_nonneg : 0 ≤ 30 + K := by positivity
    have hG_nonneg : 0 ≤ G := by
      dsimp [G]
      positivity
    have hy5_le_G : y ^ 5 ≤ G := by
      dsimp [G]
      nlinarith [pow_nonneg hy0 6, pow_nonneg hy0 7, pow_nonneg hy0 8,
        pow_nonneg hy0 9, pow_nonneg hy0 10, pow_nonneg hy0 11,
        pow_nonneg hy0 12, pow_nonneg hy0 13, pow_nonneg hy0 14,
        pow_nonneg hy0 15]
    have hcube_support :
        (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 ≤ 27 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10,
        pow_nonneg hy0 11, pow_nonneg hy0 12, pow_nonneg hy0 13,
        pow_nonneg hy0 14, pow_nonneg hy0 15]
    have hprod_support :
        (y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5) ≤ 6 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10]
    have hS_le : S ≤ (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
      dsimp [S]
      calc
        10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
            ≤ (20 + K) * y ^ 3 + (20 + K) * y ^ 4 + (20 + K) * y ^ 5 := by
              gcongr
              · linarith
              · linarith
              · linarith
        _ = (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
    have hS_cube :
        S ^ 3 ≤ (20 + K) ^ 3 * (27 * G) := by
      calc
        S ^ 3 ≤ ((20 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hS_le 3
        _ = (20 + K) ^ 3 * (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 := by ring
        _ ≤ (20 + K) ^ 3 * (27 * G) :=
          mul_le_mul_of_nonneg_left hcube_support (pow_nonneg hK20_nonneg 3)
    have hT_le :
        T ≤ (10 + K) * (30 + K) * (6 * G) := by
      have hleft : 10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * (y ^ 4 + y ^ 5) := by
        calc
          10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * y ^ 4 + (10 + K) * y ^ 5 := by
            gcongr
            · linarith
            · linarith
          _ = (10 + K) * (y ^ 4 + y ^ 5) := by ring
      have hright :
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5 ≤
            (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
        calc
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
              ≤ (30 + K) * y ^ 3 + (30 + K) * y ^ 4 + (30 + K) * y ^ 5 := by
                gcongr
                · linarith
                · linarith
                · linarith
          _ = (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
      calc
        T ≤ ((10 + K) * (y ^ 4 + y ^ 5)) *
              ((30 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) := by
          dsimp [T]
          exact mul_le_mul hleft hright (by positivity) (by positivity)
        _ = (10 + K) * (30 + K) *
              ((y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5)) := by ring
        _ ≤ (10 + K) * (30 + K) * (6 * G) := by
          gcongr
    calc
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T
          ≤ Real.exp 1 * ((20 + K) ^ 3 * (27 * G)) + K * G +
              (10 + K) * (30 + K) * (6 * G) := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hS_cube (Real.exp_pos 1).le)
              (mul_le_mul_of_nonneg_left hy5_le_G hK_nonneg)) hT_le
      _ = (27 * Real.exp 1 * (20 + K) ^ 3 + K +
            6 * (10 + K) * (30 + K)) * G := by ring
      _ = fragPermLocalL1Const * G := by
        dsimp [K]
        unfold fragPermLocalL1Const
        ring
  have hdiff :
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
        fragPermLocalL1Const * D * G := by
    calc
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
          ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
              (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := herr
      _ ≤ Real.exp 1 * D * S ^ 3 + K * D * y ^ 5 + D * T := by
        exact add_le_add (add_le_add hWcube hR_D) hprod
      _ = D * (Real.exp 1 * S ^ 3 + K * y ^ 5 + T) := by ring
      _ ≤ D * (fragPermLocalL1Const * G) :=
        mul_le_mul_of_nonneg_left hpoly hD_nonneg
      _ = fragPermLocalL1Const * D * G := by ring
  rw [fragPerm_saddleLocalRatio_eq]
  rw [hP]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
        (Complex.exp W - (1 + C + Q + C ^ 2 / 2))‖ ≤
      fragPermLocalL1Const * D * fragPermGaussianDom x
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold fragPermGaussianDom
  dsimp [D, G, y, u]
  calc
    Real.exp (-(x ^ 2) / 2) *
        ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
        ≤ Real.exp (-(x ^ 2) / 2) * (fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)) * G) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)) *
        (Real.exp (-(x ^ 2) / 2) *
          (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
            |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)) := by
      ring
