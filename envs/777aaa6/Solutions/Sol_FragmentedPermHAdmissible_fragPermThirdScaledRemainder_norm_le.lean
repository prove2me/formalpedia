-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPermThirdScaledRemainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:44:43.681221+00:00
-- url     : https://prove2.me/submissions/19c9b11d-5d09-4306-a4b1-d968405cfdbe

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
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

lemma fragPerm_exp_i_sub_one_norm_le_two_abs {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ 2 * |θ| := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_le (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
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
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace FragmentedPermHAdmissible

private lemma fragPermThird_sqrtB_sq {r : ℝ} (hb : 0 < fragPermSaddleBReal r) :
    ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) =
      (fragPermSaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private lemma fragPermThirdScaledRemainder_eq_unscaled {r x : ℝ}
    (hb : 0 < fragPermSaddleBReal r) :
    fragPermThirdScaledRemainder r x =
      fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 6) := by
  have hsqrt_ne : (Real.sqrt (fragPermSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (fragPermSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_sq := fragPermThird_sqrtB_sq hb
  have hsqrt_pow4 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 =
        (fragPermSaddleBReal r : ℂ) ^ 2 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 2 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
  have hsqrt_pow6 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
        (fragPermSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
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
  have hθ5 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 5 =
        (x : ℂ) ^ 5 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5 := by
    norm_num [Complex.ofReal_div]
    ring
  have hθ6 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 6 =
        (x : ℂ) ^ 6 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 := by
    norm_num [Complex.ofReal_div]
    ring
  unfold fragPermThirdScaledRemainder fragPermThirdScaledCubic
    fragPermThirdScaledQuartic fragPermThirdScaledFifth fragPermThirdScaledSixth
  rw [hθ3, hθ4, hθ5, hθ6, hsqrt_pow4, hsqrt_pow6]
  field_simp [hsqrt_ne, hb_ne]
  ring

private def expPoly6 (z : ℂ) : ℂ :=
  1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120 + z ^ 6 / 720

private def expTail6 (z : ℂ) : ℂ :=
  Complex.exp z - expPoly6 z

private lemma exp_sum_range_seven_eq_expPoly6 (z : ℂ) :
    (∑ m ∈ Finset.range 7, z ^ m / (m.factorial : ℂ)) = expPoly6 z := by
  norm_num [Finset.sum_range_succ, expPoly6]

private lemma expTail6_norm_le_exp6 {z : ℂ} (hz : ‖z‖ ≤ 6) :
    ‖expTail6 z‖ ≤ Real.exp 6 * ‖z‖ ^ 7 := by
  have htail :
      ‖Complex.exp z - (∑ m ∈ Finset.range 7, z ^ m / (m.factorial : ℂ))‖ ≤
        ‖z‖ ^ 7 * Real.exp ‖z‖ :=
    Complex.norm_exp_sub_sum_le_norm_mul_exp z 7
  calc
    ‖expTail6 z‖ =
        ‖Complex.exp z - (∑ m ∈ Finset.range 7, z ^ m / (m.factorial : ℂ))‖ := by
          rw [exp_sum_range_seven_eq_expPoly6]
          rfl
    _ ≤ ‖z‖ ^ 7 * Real.exp ‖z‖ := htail
    _ ≤ ‖z‖ ^ 7 * Real.exp 6 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz)
        (pow_nonneg (norm_nonneg z) 7)
    _ = Real.exp 6 * ‖z‖ ^ 7 := by ring

private lemma expTail6_nat_mul_norm_le {w : ℂ} {y : ℝ} (k : ℕ)
    (hk : k ≤ 6) (hw : ‖w‖ = y) (hy1 : y ≤ 1) :
    ‖expTail6 ((k : ℂ) * w)‖ ≤ (k : ℝ) ^ 7 * Real.exp 6 * y ^ 7 := by
  have hkw_norm : ‖(k : ℂ) * w‖ = (k : ℝ) * y := by
    rw [norm_mul, Complex.norm_natCast, hw]
  have hkw_le_six : ‖(k : ℂ) * w‖ ≤ 6 := by
    rw [hkw_norm]
    have hkreal : (k : ℝ) ≤ 6 := by exact_mod_cast hk
    nlinarith
  have hraw := expTail6_norm_le_exp6 (z := (k : ℂ) * w) hkw_le_six
  calc
    ‖expTail6 ((k : ℂ) * w)‖ ≤ Real.exp 6 * ‖(k : ℂ) * w‖ ^ 7 := hraw
    _ = Real.exp 6 * ((k : ℝ) * y) ^ 7 := by rw [hkw_norm]
    _ = (k : ℝ) ^ 7 * Real.exp 6 * y ^ 7 := by ring

private lemma complex_norm_add4_le (z1 z2 z3 z4 : ℂ) :
    ‖z1 + z2 + z3 + z4‖ ≤ ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ := by
  have h12 : ‖z1 + z2‖ ≤ ‖z1‖ + ‖z2‖ := norm_add_le z1 z2
  have h123 : ‖z1 + z2 + z3‖ ≤ ‖z1 + z2‖ + ‖z3‖ :=
    norm_add_le (z1 + z2) z3
  have h1234 : ‖z1 + z2 + z3 + z4‖ ≤ ‖z1 + z2 + z3‖ + ‖z4‖ :=
    norm_add_le (z1 + z2 + z3) z4
  nlinarith

private lemma complex_norm_add5_le (z1 z2 z3 z4 z5 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ := by
  have h4 := complex_norm_add4_le z1 z2 z3 z4
  have h5 : ‖z1 + z2 + z3 + z4 + z5‖ ≤ ‖z1 + z2 + z3 + z4‖ + ‖z5‖ :=
    norm_add_le (z1 + z2 + z3 + z4) z5
  nlinarith

private lemma complex_norm_add6_le (z1 z2 z3 z4 z5 z6 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5 + z6‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ := by
  have h5 := complex_norm_add5_le z1 z2 z3 z4 z5
  have h6 : ‖z1 + z2 + z3 + z4 + z5 + z6‖ ≤
      ‖z1 + z2 + z3 + z4 + z5‖ + ‖z6‖ :=
    norm_add_le (z1 + z2 + z3 + z4 + z5) z6
  nlinarith

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma exp_sub_one_sq_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 2 -
      (w ^ 2 + w ^ 3 + (7 / 12 : ℂ) * w ^ 4 +
        (1 / 4 : ℂ) * w ^ 5 + (31 / 360 : ℂ) * w ^ 6)‖
      ≤ 1000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  have hw_le_six : ‖w‖ ≤ 6 := by linarith
  have h2w_norm : ‖(2 : ℂ) * w‖ = 2 * y := by
    rw [norm_mul, Complex.norm_ofNat, hw]
  have h2w_le_six : ‖(2 : ℂ) * w‖ ≤ 6 := by
    rw [h2w_norm]
    nlinarith
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    simpa [T1, hw] using expTail6_norm_le_exp6 (z := w) hw_le_six
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have hraw := expTail6_norm_le_exp6 (z := (2 : ℂ) * w) h2w_le_six
    calc
      ‖T2‖ ≤ Real.exp 6 * ‖(2 : ℂ) * w‖ ^ 7 := by
        simpa [T2] using hraw
      _ = Real.exp 6 * (2 * y) ^ 7 := by rw [h2w_norm]
      _ = 128 * Real.exp 6 * y ^ 7 := by ring
      _ ≤ 200 * Real.exp 6 * y ^ 7 := by
        have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 2 -
        (w ^ 2 + w ^ 3 + (7 / 12 : ℂ) * w ^ 4 +
          (1 / 4 : ℂ) * w ^ 5 + (31 / 360 : ℂ) * w ^ 6) =
        T2 - 2 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    dsimp [T1, T2, expTail6, expPoly6]
    rw [hexp2]
    ring_nf
  rw [hdiff]
  calc
    ‖T2 - 2 * T1‖ ≤ ‖T2‖ + ‖2 * T1‖ := norm_sub_le _ _
    _ ≤ 200 * Real.exp 6 * y ^ 7 + 2 * (Real.exp 6 * y ^ 7) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact add_le_add hT2 (mul_le_mul_of_nonneg_left hT1 (by norm_num))
    _ ≤ 1000 * Real.exp 6 * y ^ 7 := by
      have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
        mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
      nlinarith

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma exp_sub_one_cube_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 3 -
      (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
        (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)‖
      ≤ 10000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  have hw_le_six : ‖w‖ ≤ 6 := by linarith
  have h2w_norm : ‖(2 : ℂ) * w‖ = 2 * y := by
    rw [norm_mul, Complex.norm_ofNat, hw]
  have h3w_norm : ‖(3 : ℂ) * w‖ = 3 * y := by
    rw [norm_mul, Complex.norm_ofNat, hw]
  have h2w_le_six : ‖(2 : ℂ) * w‖ ≤ 6 := by
    rw [h2w_norm]
    nlinarith
  have h3w_le_six : ‖(3 : ℂ) * w‖ ≤ 6 := by
    rw [h3w_norm]
    nlinarith
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    simpa [T1, hw] using expTail6_norm_le_exp6 (z := w) hw_le_six
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have hraw := expTail6_norm_le_exp6 (z := (2 : ℂ) * w) h2w_le_six
    calc
      ‖T2‖ ≤ Real.exp 6 * ‖(2 : ℂ) * w‖ ^ 7 := by
        simpa [T2] using hraw
      _ = Real.exp 6 * (2 * y) ^ 7 := by rw [h2w_norm]
      _ = 128 * Real.exp 6 * y ^ 7 := by ring
      _ ≤ 200 * Real.exp 6 * y ^ 7 := by
        have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have hraw := expTail6_norm_le_exp6 (z := (3 : ℂ) * w) h3w_le_six
    calc
      ‖T3‖ ≤ Real.exp 6 * ‖(3 : ℂ) * w‖ ^ 7 := by
        simpa [T3] using hraw
      _ = Real.exp 6 * (3 * y) ^ 7 := by rw [h3w_norm]
      _ = 2187 * Real.exp 6 * y ^ 7 := by ring
      _ ≤ 3000 * Real.exp 6 * y ^ 7 := by
        have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 3 -
        (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6) =
        T3 - 3 * T2 + 3 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    dsimp [T1, T2, T3, expTail6, expPoly6]
    rw [hexp2, hexp3]
    ring_nf
  rw [hdiff]
  calc
    ‖T3 - 3 * T2 + 3 * T1‖ ≤ ‖T3‖ + ‖3 * T2‖ + ‖3 * T1‖ := by
      calc
        ‖T3 - 3 * T2 + 3 * T1‖ ≤ ‖T3 - 3 * T2‖ + ‖3 * T1‖ := norm_add_le _ _
        _ ≤ (‖T3‖ + ‖3 * T2‖) + ‖3 * T1‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (norm_sub_le T3 (3 * T2)) ‖3 * T1‖
        _ = ‖T3‖ + ‖3 * T2‖ + ‖3 * T1‖ := by ring
    _ ≤ 3000 * Real.exp 6 * y ^ 7 +
          3 * (200 * Real.exp 6 * y ^ 7) +
            3 * (Real.exp 6 * y ^ 7) := by
      have h3T2 : ‖3 * T2‖ = 3 * ‖T2‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      have h3T1 : ‖3 * T1‖ = 3 * ‖T1‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      rw [h3T2, h3T1]
      nlinarith [hT1, hT2, hT3]
    _ ≤ 10000 * Real.exp 6 * y ^ 7 := by
      have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
        mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
      nlinarith

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma exp_sub_one_fourth_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 4 -
      (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)‖
      ≤ 100000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  let T4 : ℂ := expTail6 (4 * w)
  have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
    mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 1) (by norm_num) hw hy1
    simpa [T1] using h
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 2) (by norm_num) hw hy1
    dsimp [T2] at h
    norm_num at h
    nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 3) (by norm_num) hw hy1
    dsimp [T3] at h
    norm_num at h
    nlinarith
  have hT4 : ‖T4‖ ≤ 20000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 4) (by norm_num) hw hy1
    dsimp [T4] at h
    norm_num at h
    nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 4 -
        (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6) =
        T4 - 4 * T3 + 6 * T2 - 4 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    have hexp4 : Complex.exp (4 * w) = Complex.exp w ^ 4 := by
      simpa using Complex.exp_nat_mul w 4
    have hq :
        (Complex.exp w - 1) ^ 4 =
          Complex.exp (4 * w) - 4 * Complex.exp (3 * w) +
            6 * Complex.exp (2 * w) - 4 * Complex.exp w + 1 := by
      rw [hexp2, hexp3, hexp4]
      ring
    have hpoly :
        expPoly6 (4 * w) - 4 * expPoly6 (3 * w) + 6 * expPoly6 (2 * w) -
            4 * expPoly6 w =
          -1 + (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6) := by
      unfold expPoly6
      ring_nf
    rw [hq]
    dsimp [T1, T2, T3, T4, expTail6]
    calc
      Complex.exp (4 * w) - 4 * Complex.exp (3 * w) + 6 * Complex.exp (2 * w) -
            4 * Complex.exp w + 1 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)
          =
        Complex.exp (4 * w) - 4 * Complex.exp (3 * w) + 6 * Complex.exp (2 * w) -
          4 * Complex.exp w -
          (expPoly6 (4 * w) - 4 * expPoly6 (3 * w) + 6 * expPoly6 (2 * w) -
            4 * expPoly6 w) := by
          rw [hpoly]
          ring
      _ = Complex.exp (4 * w) - expPoly6 (4 * w) -
            4 * (Complex.exp (3 * w) - expPoly6 (3 * w)) +
            6 * (Complex.exp (2 * w) - expPoly6 (2 * w)) -
            4 * (Complex.exp w - expPoly6 w) := by ring
  rw [hdiff]
  have htri :
      ‖T4 - 4 * T3 + 6 * T2 - 4 * T1‖ ≤
        ‖T4‖ + ‖4 * T3‖ + ‖6 * T2‖ + ‖4 * T1‖ := by
    have h := complex_norm_add4_le T4 (-(4 * T3)) (6 * T2) (-(4 * T1))
    simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ‖T4 - 4 * T3 + 6 * T2 - 4 * T1‖
        ≤ ‖T4‖ + ‖4 * T3‖ + ‖6 * T2‖ + ‖4 * T1‖ := htri
    _ ≤ 20000 * Real.exp 6 * y ^ 7 +
          4 * (3000 * Real.exp 6 * y ^ 7) +
            6 * (200 * Real.exp 6 * y ^ 7) +
              4 * (Real.exp 6 * y ^ 7) := by
      have h4T3 : ‖4 * T3‖ = 4 * ‖T3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h6T2 : ‖6 * T2‖ = 6 * ‖T2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h4T1 : ‖4 * T1‖ = 4 * ‖T1‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [h4T3, h6T2, h4T1]
      nlinarith [hT1, hT2, hT3, hT4]
    _ ≤ 100000 * Real.exp 6 * y ^ 7 := by
      nlinarith

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma exp_sub_one_fifth_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)‖
      ≤ 500000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  let T4 : ℂ := expTail6 (4 * w)
  let T5 : ℂ := expTail6 (5 * w)
  have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
    mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 1) (by norm_num) hw hy1
    simpa [T1] using h
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 2) (by norm_num) hw hy1
    dsimp [T2] at h
    norm_num at h
    nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 3) (by norm_num) hw hy1
    dsimp [T3] at h
    norm_num at h
    nlinarith
  have hT4 : ‖T4‖ ≤ 20000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 4) (by norm_num) hw hy1
    dsimp [T4] at h
    norm_num at h
    nlinarith
  have hT5 : ‖T5‖ ≤ 80000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 5) (by norm_num) hw hy1
    dsimp [T5] at h
    norm_num at h
    nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6) =
        T5 - 5 * T4 + 10 * T3 - 10 * T2 + 5 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    have hexp4 : Complex.exp (4 * w) = Complex.exp w ^ 4 := by
      simpa using Complex.exp_nat_mul w 4
    have hexp5 : Complex.exp (5 * w) = Complex.exp w ^ 5 := by
      simpa using Complex.exp_nat_mul w 5
    have hq :
        (Complex.exp w - 1) ^ 5 =
          Complex.exp (5 * w) - 5 * Complex.exp (4 * w) +
            10 * Complex.exp (3 * w) - 10 * Complex.exp (2 * w) +
              5 * Complex.exp w - 1 := by
      rw [hexp2, hexp3, hexp4, hexp5]
      ring
    have hpoly :
        expPoly6 (5 * w) - 5 * expPoly6 (4 * w) + 10 * expPoly6 (3 * w) -
            10 * expPoly6 (2 * w) + 5 * expPoly6 w =
          1 + (w ^ 5 + (5 / 2 : ℂ) * w ^ 6) := by
      unfold expPoly6
      ring_nf
    rw [hq]
    dsimp [T1, T2, T3, T4, T5, expTail6]
    calc
      Complex.exp (5 * w) - 5 * Complex.exp (4 * w) + 10 * Complex.exp (3 * w) -
            10 * Complex.exp (2 * w) + 5 * Complex.exp w - 1 -
            (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)
          =
        Complex.exp (5 * w) - 5 * Complex.exp (4 * w) + 10 * Complex.exp (3 * w) -
          10 * Complex.exp (2 * w) + 5 * Complex.exp w -
          (expPoly6 (5 * w) - 5 * expPoly6 (4 * w) + 10 * expPoly6 (3 * w) -
            10 * expPoly6 (2 * w) + 5 * expPoly6 w) := by
          rw [hpoly]
          ring
      _ = Complex.exp (5 * w) - expPoly6 (5 * w) -
            5 * (Complex.exp (4 * w) - expPoly6 (4 * w)) +
            10 * (Complex.exp (3 * w) - expPoly6 (3 * w)) -
            10 * (Complex.exp (2 * w) - expPoly6 (2 * w)) +
            5 * (Complex.exp w - expPoly6 w) := by ring
  rw [hdiff]
  have htri :
      ‖T5 - 5 * T4 + 10 * T3 - 10 * T2 + 5 * T1‖ ≤
        ‖T5‖ + ‖5 * T4‖ + ‖10 * T3‖ + ‖10 * T2‖ + ‖5 * T1‖ := by
    have h := complex_norm_add5_le T5 (-(5 * T4)) (10 * T3) (-(10 * T2)) (5 * T1)
    simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ‖T5 - 5 * T4 + 10 * T3 - 10 * T2 + 5 * T1‖
        ≤ ‖T5‖ + ‖5 * T4‖ + ‖10 * T3‖ + ‖10 * T2‖ + ‖5 * T1‖ := htri
    _ ≤ 80000 * Real.exp 6 * y ^ 7 +
          5 * (20000 * Real.exp 6 * y ^ 7) +
            10 * (3000 * Real.exp 6 * y ^ 7) +
              10 * (200 * Real.exp 6 * y ^ 7) +
                5 * (Real.exp 6 * y ^ 7) := by
      have h5T4 : ‖5 * T4‖ = 5 * ‖T4‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h10T3 : ‖10 * T3‖ = 10 * ‖T3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h10T2 : ‖10 * T2‖ = 10 * ‖T2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h5T1 : ‖5 * T1‖ = 5 * ‖T1‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [h5T4, h10T3, h10T2, h5T1]
      nlinarith [hT1, hT2, hT3, hT4, hT5]
    _ ≤ 500000 * Real.exp 6 * y ^ 7 := by
      nlinarith

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma exp_sub_one_sixth_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 6 - w ^ 6‖
      ≤ 2000000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  let T4 : ℂ := expTail6 (4 * w)
  let T5 : ℂ := expTail6 (5 * w)
  let T6 : ℂ := expTail6 (6 * w)
  have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
    mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 1) (by norm_num) hw hy1
    simpa [T1] using h
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 2) (by norm_num) hw hy1
    dsimp [T2] at h
    norm_num at h
    nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 3) (by norm_num) hw hy1
    dsimp [T3] at h
    norm_num at h
    nlinarith
  have hT4 : ‖T4‖ ≤ 20000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 4) (by norm_num) hw hy1
    dsimp [T4] at h
    norm_num at h
    nlinarith
  have hT5 : ‖T5‖ ≤ 80000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 5) (by norm_num) hw hy1
    dsimp [T5] at h
    norm_num at h
    nlinarith
  have hT6 : ‖T6‖ ≤ 300000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 6) (by norm_num) hw hy1
    dsimp [T6] at h
    norm_num at h
    nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 6 - w ^ 6 =
        T6 - 6 * T5 + 15 * T4 - 20 * T3 + 15 * T2 - 6 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    have hexp4 : Complex.exp (4 * w) = Complex.exp w ^ 4 := by
      simpa using Complex.exp_nat_mul w 4
    have hexp5 : Complex.exp (5 * w) = Complex.exp w ^ 5 := by
      simpa using Complex.exp_nat_mul w 5
    have hexp6 : Complex.exp (6 * w) = Complex.exp w ^ 6 := by
      simpa using Complex.exp_nat_mul w 6
    have hq :
        (Complex.exp w - 1) ^ 6 =
          Complex.exp (6 * w) - 6 * Complex.exp (5 * w) +
            15 * Complex.exp (4 * w) - 20 * Complex.exp (3 * w) +
              15 * Complex.exp (2 * w) - 6 * Complex.exp w + 1 := by
      rw [hexp2, hexp3, hexp4, hexp5, hexp6]
      ring
    have hpoly :
        expPoly6 (6 * w) - 6 * expPoly6 (5 * w) + 15 * expPoly6 (4 * w) -
            20 * expPoly6 (3 * w) + 15 * expPoly6 (2 * w) - 6 * expPoly6 w =
          -1 + w ^ 6 := by
      unfold expPoly6
      ring_nf
    rw [hq]
    dsimp [T1, T2, T3, T4, T5, T6, expTail6]
    calc
      Complex.exp (6 * w) - 6 * Complex.exp (5 * w) + 15 * Complex.exp (4 * w) -
            20 * Complex.exp (3 * w) + 15 * Complex.exp (2 * w) -
            6 * Complex.exp w + 1 - w ^ 6
          =
        Complex.exp (6 * w) - 6 * Complex.exp (5 * w) + 15 * Complex.exp (4 * w) -
          20 * Complex.exp (3 * w) + 15 * Complex.exp (2 * w) - 6 * Complex.exp w -
          (expPoly6 (6 * w) - 6 * expPoly6 (5 * w) + 15 * expPoly6 (4 * w) -
            20 * expPoly6 (3 * w) + 15 * expPoly6 (2 * w) - 6 * expPoly6 w) := by
          rw [hpoly]
          ring
      _ = Complex.exp (6 * w) - expPoly6 (6 * w) -
            6 * (Complex.exp (5 * w) - expPoly6 (5 * w)) +
            15 * (Complex.exp (4 * w) - expPoly6 (4 * w)) -
            20 * (Complex.exp (3 * w) - expPoly6 (3 * w)) +
            15 * (Complex.exp (2 * w) - expPoly6 (2 * w)) -
            6 * (Complex.exp w - expPoly6 w) := by ring
  rw [hdiff]
  have htri :
      ‖T6 - 6 * T5 + 15 * T4 - 20 * T3 + 15 * T2 - 6 * T1‖ ≤
        ‖T6‖ + ‖6 * T5‖ + ‖15 * T4‖ + ‖20 * T3‖ +
          ‖15 * T2‖ + ‖6 * T1‖ := by
    have h := complex_norm_add6_le T6 (-(6 * T5)) (15 * T4) (-(20 * T3))
      (15 * T2) (-(6 * T1))
    simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ‖T6 - 6 * T5 + 15 * T4 - 20 * T3 + 15 * T2 - 6 * T1‖
        ≤ ‖T6‖ + ‖6 * T5‖ + ‖15 * T4‖ + ‖20 * T3‖ +
          ‖15 * T2‖ + ‖6 * T1‖ := htri
    _ ≤ 300000 * Real.exp 6 * y ^ 7 +
          6 * (80000 * Real.exp 6 * y ^ 7) +
            15 * (20000 * Real.exp 6 * y ^ 7) +
              20 * (3000 * Real.exp 6 * y ^ 7) +
                15 * (200 * Real.exp 6 * y ^ 7) +
                  6 * (Real.exp 6 * y ^ 7) := by
      have h6T5 : ‖6 * T5‖ = 6 * ‖T5‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h15T4 : ‖15 * T4‖ = 15 * ‖T4‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h20T3 : ‖20 * T3‖ = 20 * ‖T3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h15T2 : ‖15 * T2‖ = 15 * ‖T2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h6T1 : ‖6 * T1‖ = 6 * ‖T1‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [h6T5, h15T4, h20T3, h15T2, h6T1]
      nlinarith [hT1, hT2, hT3, hT4, hT5, hT6]
    _ ≤ 2000000 * Real.exp 6 * y ^ 7 := by
      nlinarith

private lemma fragPermLocalExponent_seventh_remainder_norm_le {r θ : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |θ| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4) :
    ‖fragPermLocalExponent r θ -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) * (θ : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) * (θ : ℂ) ^ 6)‖
      ≤ 1000000000 * Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8 := by
  let y : ℝ := |θ|
  let uR : ℝ := 1 - r
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  let c : ℂ := (r : ℂ) / u
  let geom : ℂ := (r : ℂ) * q / u
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let D : ℂ := (r : ℂ) ^ 3 / u ^ 4
  let P1 : ℂ := w ^ 3 / 6 + w ^ 4 / 24 + w ^ 5 / 120 + w ^ 6 / 720
  let P2 : ℂ := w ^ 3 + (7 / 12 : ℂ) * w ^ 4 + (1 / 4 : ℂ) * w ^ 5 +
    (31 / 360 : ℂ) * w ^ 6
  let P3 : ℂ := w ^ 3 + ((3 / 2 : ℂ) + c) * w ^ 4 +
    ((5 / 4 : ℂ) + 2 * c + c ^ 2) * w ^ 5 +
      ((3 / 4 : ℂ) + (13 / 6 : ℂ) * c + (5 / 2 : ℂ) * c ^ 2 + c ^ 3) *
        w ^ 6
  let P : ℂ :=
    -Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
      ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
        Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) * (θ : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) * (θ : ℂ) ^ 6
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
  have hy0 : 0 ≤ y := by dsimp [y]; exact abs_nonneg θ
  have hy1 : y ≤ 1 := by dsimp [y]; exact hθδ.trans hδle
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
  have hgeom_norm : ‖geom‖ ≤ (1 / 2 : ℝ) := by
    have hnorm_eq : ‖geom‖ = r * ‖q‖ / uR := by
      dsimp [geom, c, u, uR]
      rw [norm_div, norm_mul, hr_norm, hu_norm]
    calc
      ‖geom‖ = r * ‖q‖ / uR := hnorm_eq
      _ ≤ r * (2 * y) / uR := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq_norm hr0) hu_nonneg
      _ ≤ 1 * (2 * fragPermThirdSaddleDeltaReal r) / uR := by
        have hyδ : y ≤ fragPermThirdSaddleDeltaReal r := by simpa [y] using hθδ
        exact div_le_div_of_nonneg_right
          (mul_le_mul hrle (mul_le_mul_of_nonneg_left hyδ (by norm_num))
            (mul_nonneg (by norm_num) hy0) zero_le_one) hu_nonneg
      _ ≤ 1 / 2 := by
        rw [one_mul]
        have hδu' : 2 * fragPermThirdSaddleDeltaReal r ≤ uR / 2 := by
          have hδu0 : fragPermThirdSaddleDeltaReal r ≤ uR / 4 := by
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
  dsimp [u, w, q, geom, c] at hdecomp
  have hP_decomp : P = A * P1 + B * P2 + D * P3 := by
    have hu_eq : u = (uR : ℂ) := by
      dsimp [u, uR]
      norm_num
    have h1mr_ne : 1 - r ≠ 0 := by linarith [hr.2]
    have hw3 : w ^ 3 = -Complex.I * (θ : ℂ) ^ 3 := by
      dsimp [w]
      rw [mul_pow, Complex.I_pow_three]
      ring
    have hw4 : w ^ 4 = (θ : ℂ) ^ 4 := by
      dsimp [w]
      rw [mul_pow, Complex.I_pow_four]
      ring
    have hw5 : w ^ 5 = Complex.I * (θ : ℂ) ^ 5 := by
      dsimp [w]
      have hI5 : Complex.I ^ 5 = Complex.I := by
        calc
          Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := by ring
          _ = Complex.I := by rw [Complex.I_pow_four, one_mul]
      rw [mul_pow, hI5]
      ring
    have hw6 : w ^ 6 = -((θ : ℂ) ^ 6) := by
      dsimp [w]
      have hI6 : Complex.I ^ 6 = -1 := by
        calc
          Complex.I ^ 6 = Complex.I ^ 4 * Complex.I ^ 2 := by ring
          _ = -1 := by
            rw [Complex.I_pow_four, Complex.I_sq]
            ring
      rw [mul_pow, hI6]
      ring
    have hb3idR :
        fragPermSaddleB3Real r / 6 =
          r / (6 * uR ^ 2) + r ^ 2 / uR ^ 3 + r ^ 3 / uR ^ 4 := by
      unfold fragPermSaddleB3Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb4idR :
        fragPermSaddleB4Real r / 24 =
          r / (24 * uR ^ 2) + 7 * r ^ 2 / (12 * uR ^ 3) +
            3 * r ^ 3 / (2 * uR ^ 4) + r ^ 4 / uR ^ 5 := by
      unfold fragPermSaddleB4Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb5idR :
        fragPermSaddleB5Real r / 120 =
          r / (120 * uR ^ 2) + r ^ 2 / (4 * uR ^ 3) +
            r ^ 3 / uR ^ 4 * (5 / 4 + 2 * (r / uR) + (r / uR) ^ 2) := by
      unfold fragPermSaddleB5Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb6idR :
        fragPermSaddleB6Real r / 720 =
          r / (720 * uR ^ 2) + 31 * r ^ 2 / (360 * uR ^ 3) +
            r ^ 3 / uR ^ 4 *
              (3 / 4 + 13 / 6 * (r / uR) + 5 / 2 * (r / uR) ^ 2 +
                (r / uR) ^ 3) := by
      unfold fragPermSaddleB6Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb3id :
        ((fragPermSaddleB3Real r : ℂ) / 6) =
          ((r / (6 * uR ^ 2) + r ^ 2 / uR ^ 3 + r ^ 3 / uR ^ 4 : ℝ) : ℂ) := by
      norm_num [← Complex.ofReal_div]
      exact_mod_cast hb3idR
    have hb4id :
        ((fragPermSaddleB4Real r : ℂ) / 24) =
          ((r / (24 * uR ^ 2) + 7 * r ^ 2 / (12 * uR ^ 3) +
            3 * r ^ 3 / (2 * uR ^ 4) + r ^ 4 / uR ^ 5 : ℝ) : ℂ) := by
      norm_num [← Complex.ofReal_div]
      exact_mod_cast hb4idR
    have hb5id :
        ((fragPermSaddleB5Real r : ℂ) / 120) =
          ((r / (120 * uR ^ 2) + r ^ 2 / (4 * uR ^ 3) +
            r ^ 3 / uR ^ 4 * (5 / 4 + 2 * (r / uR) + (r / uR) ^ 2) : ℝ) : ℂ) := by
      rw [show ((fragPermSaddleB5Real r : ℂ) / 120) =
          ((fragPermSaddleB5Real r / 120 : ℝ) : ℂ) by norm_num]
      exact_mod_cast hb5idR
    have hb6id :
        ((fragPermSaddleB6Real r : ℂ) / 720) =
          ((r / (720 * uR ^ 2) + 31 * r ^ 2 / (360 * uR ^ 3) +
            r ^ 3 / uR ^ 4 *
              (3 / 4 + 13 / 6 * (r / uR) + 5 / 2 * (r / uR) ^ 2 +
                (r / uR) ^ 3) : ℝ) : ℂ) := by
      rw [show ((fragPermSaddleB6Real r : ℂ) / 720) =
          ((fragPermSaddleB6Real r / 720 : ℝ) : ℂ) by norm_num]
      exact_mod_cast hb6idR
    have hcoef3 :
        A / 6 + B + D = ((fragPermSaddleB3Real r : ℂ) / 6) := by
      rw [hb3id]
      dsimp [A, B, D]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
    have hcoef4 :
        A / 24 + (7 / 12 : ℂ) * B + ((3 / 2 : ℂ) + c) * D =
          ((fragPermSaddleB4Real r : ℂ) / 24) := by
      rw [hb4id]
      dsimp [A, B, D, c]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
      ring
    have hcoef5 :
        A / 120 + (1 / 4 : ℂ) * B + ((5 / 4 : ℂ) + 2 * c + c ^ 2) * D =
          ((fragPermSaddleB5Real r : ℂ) / 120) := by
      rw [hb5id]
      dsimp [A, B, D, c]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
    have hcoef6 :
        A / 720 + (31 / 360 : ℂ) * B +
            ((3 / 4 : ℂ) + (13 / 6 : ℂ) * c + (5 / 2 : ℂ) * c ^ 2 + c ^ 3) * D =
          ((fragPermSaddleB6Real r : ℂ) / 720) := by
      rw [hb6id]
      dsimp [A, B, D, c]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
    have hcollect :
        A * P1 + B * P2 + D * P3 =
          (A / 6 + B + D) * w ^ 3 +
          (A / 24 + (7 / 12 : ℂ) * B + ((3 / 2 : ℂ) + c) * D) * w ^ 4 +
          (A / 120 + (1 / 4 : ℂ) * B + ((5 / 4 : ℂ) + 2 * c + c ^ 2) * D) *
            w ^ 5 +
          (A / 720 + (31 / 360 : ℂ) * B +
            ((3 / 4 : ℂ) + (13 / 6 : ℂ) * c + (5 / 2 : ℂ) * c ^ 2 + c ^ 3) * D) *
            w ^ 6 := by
      dsimp [P1, P2, P3]
      ring
    rw [hcollect]
    dsimp [P]
    rw [hcoef3, hcoef4, hcoef5, hcoef6, hw3, hw4, hw5, hw6]
    ring
  have hR1 :
      ‖ExpStirling.expLocalRemainder θ - P1‖ ≤ Real.exp 6 * y ^ 7 := by
    have htail := expTail6_norm_le_exp6 (z := w) (by simpa [hw_norm] using (by linarith : y ≤ 6))
    have htail' : ‖expTail6 w‖ ≤ Real.exp 6 * y ^ 7 := by
      simpa [hw_norm] using htail
    have htail_eq : expTail6 w = ExpStirling.expLocalRemainder θ - P1 := by
      dsimp [expTail6, expPoly6, P1, w]
      rw [ExpStirling.expLocalRemainder_eq θ]
      ring_nf
      norm_num [Complex.ofReal_mul]
      ring
    simpa [htail_eq]
      using htail'
  have hR2 :
      ‖(q ^ 2 - w ^ 2) - P2‖ ≤ 1000 * Real.exp 6 * y ^ 7 := by
    have h := exp_sub_one_sq_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
    simpa [q, P2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hR3 :
      ‖q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)‖
        ≤ 10000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_cube_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hR4 :
      ‖q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)‖
        ≤ 100000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_fourth_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hR5 :
      ‖q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)‖
        ≤ 500000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_fifth_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hR6 :
      ‖q ^ 6 - w ^ 6‖ ≤ 2000000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_sixth_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hA_norm : ‖A‖ = r / uR ^ 2 := by
    dsimp [A, u, uR]
    rw [norm_div, norm_pow, hr_norm, hu_norm]
  have hB_norm : ‖B‖ = r ^ 2 / uR ^ 3 := by
    dsimp [B, u, uR]
    rw [norm_div, norm_pow, norm_pow, hr_norm, hu_norm]
  have hD_norm : ‖D‖ = r ^ 3 / uR ^ 4 := by
    dsimp [D, u, uR]
    rw [norm_div, norm_pow, norm_pow, hr_norm, hu_norm]
  have hc_norm : ‖c‖ = r / uR := by
    dsimp [c, u, uR]
    rw [norm_div, hr_norm, hu_norm]
  have hden8_pos : 0 < uR ^ 8 := by positivity
  have hpow_le {k : ℕ} (hk : k ≤ 8) :
      uR ^ 8 ≤ uR ^ k := by
    have hsplit : uR ^ 8 = uR ^ k * uR ^ (8 - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hsplit]
    have hpow_nonneg : 0 ≤ uR ^ k := pow_nonneg hu_nonneg k
    have hrest_le_one : uR ^ (8 - k) ≤ 1 := by
      calc
        uR ^ (8 - k) ≤ 1 ^ (8 - k) := pow_le_pow_left₀ hu_nonneg hu_le_one _
        _ = 1 := by simp
    exact mul_le_of_le_one_right hpow_nonneg hrest_le_one
  have hdiv_le8 {k : ℕ} (hk : k ≤ 8) {C : ℝ} (hC : 0 ≤ C) :
      C / uR ^ k ≤ C / uR ^ 8 :=
    div_le_div_of_nonneg_left hC hden8_pos (hpow_le hk)
  have hAterm :
      ‖A * (ExpStirling.expLocalRemainder θ - P1)‖
        ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
    calc
      ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ =
          ‖A‖ * ‖ExpStirling.expLocalRemainder θ - P1‖ := norm_mul _ _
      _ ≤ (r / uR ^ 2) * (Real.exp 6 * y ^ 7) :=
        mul_le_mul hA_norm.le hR1 (norm_nonneg _) (by positivity)
      _ ≤ Real.exp 6 * y ^ 7 / uR ^ 2 := by
        have hbase_nonneg : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        have hrbase : r * (Real.exp 6 * y ^ 7) ≤ 1 * (Real.exp 6 * y ^ 7) :=
          mul_le_mul_of_nonneg_right hrle hbase_nonneg
        calc
          (r / uR ^ 2) * (Real.exp 6 * y ^ 7) =
              (r * (Real.exp 6 * y ^ 7)) / uR ^ 2 := by ring
          _ ≤ (1 * (Real.exp 6 * y ^ 7)) / uR ^ 2 :=
              div_le_div_of_nonneg_right hrbase (pow_nonneg hu_nonneg 2)
          _ = Real.exp 6 * y ^ 7 / uR ^ 2 := by ring
      _ ≤ Real.exp 6 * y ^ 7 / uR ^ 8 :=
        hdiv_le8 (by norm_num : 2 ≤ 8)
          (mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7))
      _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)])
          (pow_nonneg hu_nonneg 8)
  have hBterm :
      ‖B * ((q ^ 2 - w ^ 2) - P2)‖
        ≤ 1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
    calc
      ‖B * ((q ^ 2 - w ^ 2) - P2)‖ =
          ‖B‖ * ‖(q ^ 2 - w ^ 2) - P2‖ := norm_mul _ _
      _ ≤ (r ^ 2 / uR ^ 3) * (1000 * Real.exp 6 * y ^ 7) :=
        mul_le_mul hB_norm.le hR2 (norm_nonneg _) (by positivity)
      _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 3 := by
        have hr2le : r ^ 2 ≤ 1 := by nlinarith [hr0, hrle]
        have hbase_nonneg : 0 ≤ 1000 * Real.exp 6 * y ^ 7 :=
          mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 6).le)
            (pow_nonneg hy0 7)
        have hrbase : r ^ 2 * (1000 * Real.exp 6 * y ^ 7) ≤
            1 * (1000 * Real.exp 6 * y ^ 7) :=
          mul_le_mul_of_nonneg_right hr2le hbase_nonneg
        calc
          (r ^ 2 / uR ^ 3) * (1000 * Real.exp 6 * y ^ 7) =
              (r ^ 2 * (1000 * Real.exp 6 * y ^ 7)) / uR ^ 3 := by ring
          _ ≤ (1 * (1000 * Real.exp 6 * y ^ 7)) / uR ^ 3 :=
              div_le_div_of_nonneg_right hrbase (pow_nonneg hu_nonneg 3)
          _ = 1000 * Real.exp 6 * y ^ 7 / uR ^ 3 := by ring
      _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 :=
        hdiv_le8 (by norm_num : 3 ≤ 8)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 6).le)
            (pow_nonneg hy0 7))
      _ ≤ 1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000)
            (Real.exp_pos 6).le) (pow_nonneg hy0 7)])
          (pow_nonneg hu_nonneg 8)
  have hgeom_series :
      q ^ 3 * (1 - geom)⁻¹ - P3 =
        (q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)) +
        c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)) +
        c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)) +
        c ^ 3 * (q ^ 6 - w ^ 6) +
        c ^ 4 * q ^ 7 * (1 - geom)⁻¹ := by
    have hgeom_cq : geom = c * q := by
      dsimp [geom, c]
      field_simp [hu_ne]
    have hcq_ne : (1 : ℂ) - c * q ≠ 0 := by
      simpa [hgeom_cq] using hgeom_ne
    let g : ℂ := c * q
    have hg_ne : (1 : ℂ) - g ≠ 0 := by
      simpa [g] using hcq_ne
    have hginv :
        (1 - g)⁻¹ = 1 + g + g ^ 2 + g ^ 3 + g ^ 4 * (1 - g)⁻¹ := by
      field_simp [hg_ne]
      ring
    calc
      q ^ 3 * (1 - geom)⁻¹ - P3 =
          q ^ 3 * (1 - c * q)⁻¹ - P3 := by rw [hgeom_cq]
      _ = q ^ 3 * (1 + g + g ^ 2 + g ^ 3 + g ^ 4 * (1 - g)⁻¹) - P3 := by
          have hginv' :
              (1 - c * q)⁻¹ =
                1 + c * q + (c * q) ^ 2 + (c * q) ^ 3 +
                  (c * q) ^ 4 * (1 - c * q)⁻¹ := by
            simpa [g] using hginv
          change q ^ 3 * (1 - c * q)⁻¹ - P3 =
            q ^ 3 * (1 + c * q + (c * q) ^ 2 + (c * q) ^ 3 +
              (c * q) ^ 4 * (1 - c * q)⁻¹) - P3
          exact congrArg (fun z : ℂ => q ^ 3 * z - P3) hginv'
      _ =
        (q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)) +
        c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)) +
        c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)) +
        c ^ 3 * (q ^ 6 - w ^ 6) +
        c ^ 4 * q ^ 7 * (1 - geom)⁻¹ := by
          rw [hgeom_cq]
          dsimp [P3, g]
          ring
  have hc_le : ‖c‖ ≤ 1 / uR := by
    rw [hc_norm]
    exact div_le_div_of_nonneg_right hrle hu_nonneg
  have hD_le : ‖D‖ ≤ 1 / uR ^ 4 := by
    rw [hD_norm]
    have hr3le : r ^ 3 ≤ 1 := by
      nlinarith [hr0, hrle, sq_nonneg r, sq_nonneg (1 - r)]
    exact div_le_div_of_nonneg_right hr3le (pow_nonneg hu_nonneg 4)
  have hDbracket :
      ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖
        ≤ 100000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
    have htail :
        ‖c ^ 4 * q ^ 7 * (1 - geom)⁻¹‖
          ≤ 1000 * y ^ 7 / uR ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have hc4 : ‖c‖ ^ 4 ≤ (1 / uR) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg c) hc_le 4
      have hq7 : ‖q‖ ^ 7 ≤ (2 * y) ^ 7 :=
        pow_le_pow_left₀ (norm_nonneg q) hq_norm 7
      calc
        ‖c‖ ^ 4 * ‖q‖ ^ 7 * ‖(1 - geom)⁻¹‖
            ≤ (1 / uR) ^ 4 * (2 * y) ^ 7 * 2 := by
          exact mul_le_mul (mul_le_mul hc4 hq7 (pow_nonneg (norm_nonneg q) 7)
            (pow_nonneg (by positivity) 4)) hinv_geom_norm (norm_nonneg _) (by positivity)
        _ = 256 * y ^ 7 / uR ^ 4 := by field_simp [huR_ne]; ring
        _ ≤ 1000 * y ^ 7 / uR ^ 4 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (256 : ℝ) ≤ 1000)
              (pow_nonneg hy0 7))
            (pow_nonneg hu_nonneg 4)
    have hbr :
        ‖q ^ 3 * (1 - geom)⁻¹ - P3‖
          ≤ 10000000 * Real.exp 6 * y ^ 7 / uR ^ 4 := by
      rw [hgeom_series]
      calc
        ‖(q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
            (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)) +
          c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)) +
          c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)) +
          c ^ 3 * (q ^ 6 - w ^ 6) +
          c ^ 4 * q ^ 7 * (1 - geom)⁻¹‖
            ≤
          ‖q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
            (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)‖ +
          ‖c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6))‖ +
          ‖c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6))‖ +
          ‖c ^ 3 * (q ^ 6 - w ^ 6)‖ +
          ‖c ^ 4 * q ^ 7 * (1 - geom)⁻¹‖ :=
            complex_norm_add5_le _ _ _ _ _
        _ ≤ 10000 * Real.exp 6 * y ^ 7 +
            (1 / uR) * (100000 * Real.exp 6 * y ^ 7) +
            (1 / uR) ^ 2 * (500000 * Real.exp 6 * y ^ 7) +
            (1 / uR) ^ 3 * (2000000 * Real.exp 6 * y ^ 7) +
            1000 * y ^ 7 / uR ^ 4 := by
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
          exact add_le_add (add_le_add (add_le_add (add_le_add hR3
            (mul_le_mul hc_le hR4 (norm_nonneg _) (by positivity)))
            (mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc_le 2) hR5
              (norm_nonneg _) (by positivity)))
            (mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc_le 3) hR6
              (norm_nonneg _) (by positivity))) htail
        _ ≤ 10000000 * Real.exp 6 * y ^ 7 / uR ^ 4 := by
          let C : ℝ := Real.exp 6 * y ^ 7
          have hbase : 0 ≤ C := by
            dsimp [C]
            exact mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
          have hEge1 : 1 ≤ Real.exp 6 := by
            calc
              (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
              _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
          have hpow_le4 {k : ℕ} (hk : k ≤ 4) :
              uR ^ 4 ≤ uR ^ k := by
            have hsplit : uR ^ 4 = uR ^ k * uR ^ (4 - k) := by
              rw [← pow_add, Nat.add_sub_of_le hk]
            rw [hsplit]
            have hpow_nonneg : 0 ≤ uR ^ k := pow_nonneg hu_nonneg k
            have hrest_le_one : uR ^ (4 - k) ≤ 1 := by
              calc
                uR ^ (4 - k) ≤ 1 ^ (4 - k) :=
                  pow_le_pow_left₀ hu_nonneg hu_le_one _
                _ = 1 := by simp
            exact mul_le_of_le_one_right hpow_nonneg hrest_le_one
          have hden4_pos : 0 < uR ^ 4 := by positivity
          have hdiv_le4 {k : ℕ} (hk : k ≤ 4) {D0 : ℝ} (hD0 : 0 ≤ D0) :
              D0 / uR ^ k ≤ D0 / uR ^ 4 :=
            div_le_div_of_nonneg_left hD0 hden4_pos (hpow_le4 hk)
          have h1 :
              10000 * C ≤ 10000 * C / uR ^ 4 := by
            simpa using hdiv_le4 (by norm_num : 0 ≤ 4)
              (D0 := 10000 * C)
              (mul_nonneg (by norm_num) hbase)
          have h2 :
              (1 / uR) * (100000 * C) ≤ 100000 * C / uR ^ 4 := by
            calc
              (1 / uR) * (100000 * C) = (100000 * C) / uR ^ 1 := by
                field_simp [huR_ne]
              _ ≤ 100000 * C / uR ^ 4 :=
                hdiv_le4 (by norm_num : 1 ≤ 4)
                  (mul_nonneg (by norm_num) hbase)
          have h3 :
              (1 / uR) ^ 2 * (500000 * C) ≤ 500000 * C / uR ^ 4 := by
            calc
              (1 / uR) ^ 2 * (500000 * C) = (500000 * C) / uR ^ 2 := by
                field_simp [huR_ne]
              _ ≤ 500000 * C / uR ^ 4 :=
                hdiv_le4 (by norm_num : 2 ≤ 4)
                  (mul_nonneg (by norm_num) hbase)
          have h4 :
              (1 / uR) ^ 3 * (2000000 * C) ≤ 2000000 * C / uR ^ 4 := by
            calc
              (1 / uR) ^ 3 * (2000000 * C) = (2000000 * C) / uR ^ 3 := by
                field_simp [huR_ne]
              _ ≤ 2000000 * C / uR ^ 4 :=
                hdiv_le4 (by norm_num : 3 ≤ 4)
                  (mul_nonneg (by norm_num) hbase)
          have hyC : y ^ 7 ≤ C := by
            dsimp [C]
            calc
              y ^ 7 = 1 * y ^ 7 := by ring
              _ ≤ Real.exp 6 * y ^ 7 :=
                mul_le_mul_of_nonneg_right hEge1 (pow_nonneg hy0 7)
          have h5 :
              1000 * y ^ 7 / uR ^ 4 ≤ 1000 * C / uR ^ 4 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hyC (by norm_num))
              (pow_nonneg hu_nonneg 4)
          have hsum :
              10000 * C +
                (1 / uR) * (100000 * C) +
                (1 / uR) ^ 2 * (500000 * C) +
                (1 / uR) ^ 3 * (2000000 * C) +
                1000 * y ^ 7 / uR ^ 4 ≤
              10000 * C / uR ^ 4 +
                100000 * C / uR ^ 4 +
                500000 * C / uR ^ 4 +
                2000000 * C / uR ^ 4 +
                1000 * C / uR ^ 4 := by
            nlinarith [h1, h2, h3, h4, h5]
          have hdenAtom :
              0 ≤ C / uR ^ 4 := div_nonneg hbase (pow_nonneg hu_nonneg 4)
          calc
            10000 * Real.exp 6 * y ^ 7 +
                (1 / uR) * (100000 * Real.exp 6 * y ^ 7) +
                (1 / uR) ^ 2 * (500000 * Real.exp 6 * y ^ 7) +
                (1 / uR) ^ 3 * (2000000 * Real.exp 6 * y ^ 7) +
                1000 * y ^ 7 / uR ^ 4
                =
              10000 * C +
                (1 / uR) * (100000 * C) +
                (1 / uR) ^ 2 * (500000 * C) +
                (1 / uR) ^ 3 * (2000000 * C) +
                1000 * y ^ 7 / uR ^ 4 := by
                  dsimp [C]
                  ring
            _ ≤ 10000 * C / uR ^ 4 +
                100000 * C / uR ^ 4 +
                500000 * C / uR ^ 4 +
                2000000 * C / uR ^ 4 +
                1000 * C / uR ^ 4 := hsum
            _ ≤ 10000000 * C / uR ^ 4 := by
              calc
                10000 * C / uR ^ 4 + 100000 * C / uR ^ 4 +
                    500000 * C / uR ^ 4 + 2000000 * C / uR ^ 4 +
                    1000 * C / uR ^ 4
                    =
                  (2611000 : ℝ) * (C / uR ^ 4) := by ring
                _ ≤ 10000000 * (C / uR ^ 4) :=
                  mul_le_mul_of_nonneg_right (by norm_num) hdenAtom
                _ = 10000000 * C / uR ^ 4 := by ring
            _ = 10000000 * Real.exp 6 * y ^ 7 / uR ^ 4 := by
              dsimp [C]
              ring
    calc
      ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ =
          ‖D‖ * ‖q ^ 3 * (1 - geom)⁻¹ - P3‖ := norm_mul _ _
      _ ≤ (1 / uR ^ 4) * (10000000 * Real.exp 6 * y ^ 7 / uR ^ 4) :=
        mul_le_mul hD_le hbr (norm_nonneg _) (by positivity)
      _ = 10000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        field_simp [huR_ne]
      _ ≤ 100000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10000000)
            (Real.exp_pos 6).le) (pow_nonneg hy0 7)])
          (pow_nonneg hu_nonneg 8)
  have hmain_eq :
      fragPermLocalExponent r θ - P =
        A * (ExpStirling.expLocalRemainder θ - P1) +
          B * ((q ^ 2 - w ^ 2) - P2) +
            D * (q ^ 3 * (1 - geom)⁻¹ - P3) := by
    rw [hdecomp, hP_decomp]
    ring
  rw [show fragPermLocalExponent r θ -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) * (θ : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) * (θ : ℂ) ^ 6) =
        fragPermLocalExponent r θ - P by rfl]
  rw [hmain_eq]
  calc
    ‖A * (ExpStirling.expLocalRemainder θ - P1) +
          B * ((q ^ 2 - w ^ 2) - P2) +
            D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖
        ≤ ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
            ‖B * ((q ^ 2 - w ^ 2) - P2)‖ +
            ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := by
          calc
            ‖A * (ExpStirling.expLocalRemainder θ - P1) +
                B * ((q ^ 2 - w ^ 2) - P2) +
                  D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖
                ≤ ‖A * (ExpStirling.expLocalRemainder θ - P1) +
                    B * ((q ^ 2 - w ^ 2) - P2)‖ +
                    ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := norm_add_le _ _
            _ ≤ (‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
                  ‖B * ((q ^ 2 - w ^ 2) - P2)‖) +
                    ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := by
                have hAB :
                    ‖A * (ExpStirling.expLocalRemainder θ - P1) +
                      B * ((q ^ 2 - w ^ 2) - P2)‖ ≤
                    ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
                      ‖B * ((q ^ 2 - w ^ 2) - P2)‖ :=
                  norm_add_le _ _
                exact add_le_add_left hAB _
            _ = ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
                ‖B * ((q ^ 2 - w ^ 2) - P2)‖ +
                  ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := by rfl
    _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
          1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
            100000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact add_le_add (add_le_add hAterm hBterm) hDbracket
    _ ≤ 1000000000 * Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8 := by
        let Z : ℝ := Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8
        have hden_nonneg : 0 ≤ (1 - r) ^ 8 := by positivity
        have hCnon : 0 ≤ Real.exp 6 * |θ| ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg (abs_nonneg θ) 7)
        have hZ : 0 ≤ Z := by
          dsimp [Z]
          exact div_nonneg hCnon hden_nonneg
        calc
          1000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
              1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
              100000000 * Real.exp 6 * y ^ 7 / uR ^ 8
              =
            (101001000 : ℝ) * Z := by
              dsimp [Z, y, uR]
              ring
          _ ≤ 1000000000 * Z :=
            mul_le_mul_of_nonneg_right (by norm_num) hZ
          _ = 1000000000 * Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8 := by
            dsimp [Z]
            ring

private lemma fragPerm_rpow_calc_five_halves {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 8) * (2 * u ^ (3 / 2 : ℝ)) ^ 7 =
      128 * u ^ (5 / 2 : ℝ) := by
  have hun : 0 ≤ u := hu.le
  have hpow :
      (u ^ (3 / 2 : ℝ)) ^ 7 = u ^ (21 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hun]
    norm_num
  calc
    (1 / u ^ 8) * (2 * u ^ (3 / 2 : ℝ)) ^ 7
        = 128 * (u ^ (21 / 2 : ℝ) / u ^ 8) := by
          rw [mul_pow, hpow]
          ring
    _ = 128 * u ^ (5 / 2 : ℝ) := by
      rw [show u ^ 8 = u ^ (8 : ℝ) by exact (Real.rpow_natCast u 8).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hun (8 : ℝ)]
      rw [← Real.rpow_add hu]
      norm_num

end FragmentedPermHAdmissible
end

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
theorem solution {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4) :
    ‖fragPermThirdScaledRemainder r x‖ ≤
      fragPermThirdScaledRemainderConst * (1 - r) ^ (5 / 2 : ℝ) * |x| ^ 7 := by
  let u : ℝ := 1 - r
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hrem := fragPermLocalExponent_seventh_remainder_norm_le
    (r := r) (θ := x / Real.sqrt (fragPermSaddleBReal r)) hr hθδ hδle hδu
  rw [fragPermThirdScaledRemainder_eq_unscaled hbpos]
  have hsqrt_lower :
      (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) ≤
        Real.sqrt (fragPermSaddleBReal r) := by
    simpa [u] using fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  have hlower_pos : 0 < (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) := by
    positivity
  have hupow_pos : 0 < u ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hu_pos _
  have hθ_abs_le :
      |x / Real.sqrt (fragPermSaddleBReal r)| ≤
        2 * u ^ (3 / 2 : ℝ) * |x| := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    calc
      |x| / Real.sqrt (fragPermSaddleBReal r) ≤
          |x| / ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) :=
            div_le_div_of_nonneg_left (abs_nonneg x) hlower_pos hsqrt_lower
      _ = 2 * u ^ (3 / 2 : ℝ) * |x| := by
        rw [Real.rpow_neg hu_nonneg (3 / 2 : ℝ)]
        field_simp [hupow_pos.ne']
  have hθ7_le :
      |x / Real.sqrt (fragPermSaddleBReal r)| ^ 7 ≤
        (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 7
  have hscale :
      (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8 =
        128 * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by
    calc
      (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8 =
          ((2 * u ^ (3 / 2 : ℝ)) ^ 7 / u ^ 8) * |x| ^ 7 := by ring
      _ = ((1 / u ^ 8) * (2 * u ^ (3 / 2 : ℝ)) ^ 7) * |x| ^ 7 := by ring
      _ = 128 * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by
        rw [fragPerm_rpow_calc_five_halves hu_pos]
  have hconst_nonneg : 0 ≤ 1000000000 * Real.exp 6 :=
    mul_nonneg (by norm_num) (Real.exp_pos 6).le
  have hu8_nonneg : 0 ≤ u ^ 8 := pow_nonneg hu_nonneg 8
  calc
    ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 6)‖
        ≤ 1000000000 * Real.exp 6 *
            |x / Real.sqrt (fragPermSaddleBReal r)| ^ 7 / (1 - r) ^ 8 := hrem
    _ ≤ 1000000000 * Real.exp 6 *
          (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8 := by
        dsimp [u]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hθ7_le hconst_nonneg) hu8_nonneg
    _ = 1000000000 * Real.exp 6 *
          ((2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8) := by ring
    _ = 1000000000 * Real.exp 6 *
          (128 * u ^ (5 / 2 : ℝ) * |x| ^ 7) := by rw [hscale]
    _ ≤ fragPermThirdScaledRemainderConst * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by
      unfold fragPermThirdScaledRemainderConst
      have htail_nonneg : 0 ≤ u ^ (5 / 2 : ℝ) * |x| ^ 7 := by positivity
      calc
        1000000000 * Real.exp 6 *
            (128 * u ^ (5 / 2 : ℝ) * |x| ^ 7)
            = (128000000000 * Real.exp 6) *
                (u ^ (5 / 2 : ℝ) * |x| ^ 7) := by ring
        _ ≤ (200000000000 * Real.exp 6) *
              (u ^ (5 / 2 : ℝ) * |x| ^ 7) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos 6).le)
            htail_nonneg
        _ = (200000000000 * Real.exp 6) * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by ring
    _ = fragPermThirdScaledRemainderConst * (1 - r) ^ (5 / 2 : ℝ) * |x| ^ 7 := by
      dsimp [u]
