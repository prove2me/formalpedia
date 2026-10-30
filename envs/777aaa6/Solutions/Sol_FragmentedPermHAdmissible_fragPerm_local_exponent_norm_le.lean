-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPerm_local_exponent_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:42:59.958718+00:00
-- url     : https://prove2.me/submissions/113c1880-3b11-405a-b8b8-82a4b4633474

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
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

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 800000 in
theorem solution
    {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ_le_one : fragPermSaddleDeltaReal r ≤ 1)
    (hδ_le_u_quarter : fragPermSaddleDeltaReal r ≤ (1 - r) / 4)
    (hθ : |θ| ≤ fragPermSaddleDeltaReal r) :
    ‖fragPermLocalExponent r θ‖ ≤
      fragPermLocalConstant * ((fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4) := by
  let δ : ℝ := fragPermSaddleDeltaReal r
  let uR : ℝ := 1 - r
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  let y : ℂ := (r : ℂ) * q / u
  have hu_pos : 0 < uR := by dsimp [uR]; linarith [hr1]
  have hu_nonneg : 0 ≤ uR := hu_pos.le
  have hu_le_one : uR ≤ 1 := by dsimp [uR]; linarith [hr0]
  have hu_ne : u ≠ 0 := by
    dsimp [u, uR] at *
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hr_norm : ‖(r : ℂ)‖ = r :=
    (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
  have hu_norm : ‖u‖ = uR := by
    dsimp [u, uR]
    have hcoerce : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hcoerce]
    exact (RCLike.norm_ofReal (K := ℂ) (1 - r)).trans (abs_of_pos hu_pos)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, fragPermSaddleDeltaReal]
    exact Real.rpow_nonneg hu_nonneg _
  have hθ_one : |θ| ≤ 1 := hθ.trans hδ_le_one
  have hθ_nonneg : 0 ≤ |θ| := abs_nonneg θ
  have hθ2δ2 : |θ| ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ hθ_nonneg (by simpa [δ] using hθ) 2
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ hθ_nonneg (by simpa [δ] using hθ) 3
  have hq_norm : ‖q‖ ≤ 2 * |θ| := by
    simpa [q, w] using fragPerm_exp_i_sub_one_norm_le_two_abs hθ_one
  have hq_norm_delta : ‖q‖ ≤ 2 * δ := by
    exact hq_norm.trans (mul_le_mul_of_nonneg_left (by simpa [δ] using hθ)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hy_norm : ‖y‖ ≤ (1 / 2 : ℝ) := by
    have hnorm_eq : ‖y‖ = r * ‖q‖ / uR := by
      dsimp [y, u, uR]
      rw [norm_div, norm_mul]
      rw [hr_norm, hu_norm]
    calc
      ‖y‖ = r * ‖q‖ / uR := hnorm_eq
      _ ≤ r * (2 * δ) / uR := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq_norm_delta hr0) hu_nonneg
      _ ≤ 1 * (2 * δ) / uR := by
        have hr_le_one : r ≤ 1 := hr1.le
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hr_le_one (by positivity : 0 ≤ 2 * δ)) hu_nonneg
      _ ≤ 1 / 2 := by
        have hδu : 2 * δ ≤ uR / 2 := by linarith [hδ_le_u_quarter]
        rw [one_mul]
        have hu_neR : uR ≠ 0 := hu_pos.ne'
        rw [div_le_iff₀ hu_pos]
        nlinarith
  have hy_ne : (1 : ℂ) - y ≠ 0 := by
    intro hzero
    have hy_eq : y = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [hy_eq] using hy_norm
    norm_num at this
  have hdecomp := fragPermLocalExponent_decomp (r := r) (θ := θ) hr1 hy_ne
  dsimp [u, w, q, y] at hdecomp
  rw [hdecomp]
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let C : ℂ := (r : ℂ) ^ 3 / u ^ 4 * q ^ 3 * (1 - y)⁻¹
  have hη : ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 1 * |θ| ^ 3 :=
    ExpStirling.expLocalRemainder_norm_le_exp_one θ hθ_one
  have hA_norm : ‖A‖ = r / uR ^ 2 := by
    dsimp [A, u, uR]
    rw [norm_div, norm_pow]
    rw [hr_norm, hu_norm]
  have hB_norm : ‖B‖ = r ^ 2 / uR ^ 3 := by
    dsimp [B, u, uR]
    rw [norm_div, norm_pow, norm_pow]
    rw [hr_norm, hu_norm]
  have hCcoef_norm : ‖((r : ℂ) ^ 3 / u ^ 4)‖ = r ^ 3 / uR ^ 4 := by
    dsimp [u, uR]
    rw [norm_div, norm_pow, norm_pow]
    rw [hr_norm, hu_norm]
  have hterm1 :
      ‖A * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 1 * δ ^ 3 / uR ^ 4 := by
    rw [norm_mul, hA_norm]
    calc
      r / uR ^ 2 * ‖ExpStirling.expLocalRemainder θ‖
          ≤ r / uR ^ 2 * (Real.exp 1 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hη (by positivity)
      _ ≤ r / uR ^ 2 * (Real.exp 1 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 1).le) (by positivity)
      _ ≤ Real.exp 1 * δ ^ 3 / uR ^ 4 := by
        have hr_le_one : r ≤ 1 := hr1.le
        have hδ3_nonneg : 0 ≤ δ ^ 3 := by positivity
        have hu2_le_one : uR ^ 2 ≤ 1 := by nlinarith [hu_nonneg, hu_le_one]
        have hru2_le_one : r * uR ^ 2 ≤ 1 := by nlinarith [hr0, hr_le_one, hu2_le_one]
        field_simp [hu_pos.ne']
        nlinarith [hru2_le_one, hδ3_nonneg, Real.exp_pos 1]
  have hq_sub_w : ‖q - w‖ ≤ δ ^ 2 := by
    have hbase := fragPerm_exp_i_sub_one_sub_id_norm_le_sq hθ_one
    calc
      ‖q - w‖ = ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ := by
        dsimp [q, w]
      _ ≤ |θ| ^ 2 := hbase
      _ ≤ δ ^ 2 := hθ2δ2
  have hq_plus_w : ‖q + w‖ ≤ 3 * δ := by
    calc
      ‖q + w‖ ≤ ‖q‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 2 * δ + δ := by
        have hw_norm : ‖w‖ = |θ| := by dsimp [w]; simp
        rw [hw_norm]
        exact add_le_add hq_norm_delta (by simpa [δ] using hθ)
      _ = 3 * δ := by ring
  have hq_sq_sub : ‖q ^ 2 - w ^ 2‖ ≤ 3 * δ ^ 3 := by
    have hfac : q ^ 2 - w ^ 2 = (q - w) * (q + w) := by ring
    rw [hfac, norm_mul]
    calc
      ‖q - w‖ * ‖q + w‖ ≤ δ ^ 2 * (3 * δ) :=
        mul_le_mul hq_sub_w hq_plus_w (norm_nonneg _) (by positivity)
      _ = 3 * δ ^ 3 := by ring
  have hterm2 :
      ‖B * (q ^ 2 - w ^ 2)‖ ≤ 3 * δ ^ 3 / uR ^ 4 := by
    rw [norm_mul, hB_norm]
    calc
      r ^ 2 / uR ^ 3 * ‖q ^ 2 - w ^ 2‖
          ≤ r ^ 2 / uR ^ 3 * (3 * δ ^ 3) :=
        mul_le_mul_of_nonneg_left hq_sq_sub (by positivity)
      _ ≤ 3 * δ ^ 3 / uR ^ 4 := by
        have hr2_le_one : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1.le]
        have hδ3_nonneg : 0 ≤ δ ^ 3 := by positivity
        have hru_le_one : r ^ 2 * uR ≤ 1 := by nlinarith [hr2_le_one, hu_nonneg, hu_le_one]
        field_simp [hu_pos.ne']
        nlinarith [hru_le_one, hδ3_nonneg]
  have hinv_norm : ‖(1 - y)⁻¹‖ ≤ 2 := by
    have hdist : (1 / 2 : ℝ) ≤ ‖1 - y‖ := by
      calc
        (1 / 2 : ℝ) ≤ 1 - ‖y‖ := by linarith [hy_norm]
        _ ≤ ‖(1 : ℂ) - y‖ := by
          have h := norm_sub_norm_le (1 : ℂ) y
          have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by norm_num
          rw [hone] at h
          linarith
    rw [norm_inv]
    have hnorm_pos : 0 < ‖(1 : ℂ) - y‖ := norm_pos_iff.mpr hy_ne
    rw [inv_le_comm₀ hnorm_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hdist]
  have hq3 : ‖q ^ 3‖ ≤ (2 * δ) ^ 3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg q) hq_norm_delta 3
  have hterm3 :
      ‖C‖ ≤ 16 * δ ^ 3 / uR ^ 4 := by
    dsimp [C]
    rw [norm_mul, norm_mul, hCcoef_norm]
    calc
      r ^ 3 / uR ^ 4 * ‖q ^ 3‖ * ‖(1 - y)⁻¹‖
          ≤ r ^ 3 / uR ^ 4 * ((2 * δ) ^ 3) * 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hq3 (by positivity)) hinv_norm
          (norm_nonneg _) (by positivity)
      _ ≤ 16 * δ ^ 3 / uR ^ 4 := by
        have hr3_le_one : r ^ 3 ≤ 1 := by nlinarith [hr0, hr1.le]
        have hδ3_nonneg : 0 ≤ δ ^ 3 := by positivity
        field_simp [hu_pos.ne']
        nlinarith [hr3_le_one, hδ3_nonneg]
  have hsum :
      ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C‖ ≤
        (Real.exp 1 + 3 + 16) * δ ^ 3 / uR ^ 4 := by
    calc
      ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C‖
          ≤ ‖A * ExpStirling.expLocalRemainder θ‖ +
              ‖B * (q ^ 2 - w ^ 2)‖ + ‖C‖ := by
        calc
          ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C‖
              ≤ ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2)‖ + ‖C‖ :=
            norm_add_le _ _
          _ ≤ (‖A * ExpStirling.expLocalRemainder θ‖ +
                  ‖B * (q ^ 2 - w ^ 2)‖) + ‖C‖ :=
            by
              have h := norm_add_le (A * ExpStirling.expLocalRemainder θ)
                (B * (q ^ 2 - w ^ 2))
              nlinarith
          _ = ‖A * ExpStirling.expLocalRemainder θ‖ +
              ‖B * (q ^ 2 - w ^ 2)‖ + ‖C‖ := by ring
      _ ≤ Real.exp 1 * δ ^ 3 / uR ^ 4 + 3 * δ ^ 3 / uR ^ 4 +
            16 * δ ^ 3 / uR ^ 4 := add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = (Real.exp 1 + 3 + 16) * δ ^ 3 / uR ^ 4 := by ring
  refine hsum.trans ?_
  have hnonneg : 0 ≤ δ ^ 3 / uR ^ 4 := by positivity
  have hconst : Real.exp 1 + 3 + 16 ≤ 100 * Real.exp 1 := by
    have hone_le : (1 : ℝ) ≤ Real.exp 1 := by
      exact Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    nlinarith
  calc
    (Real.exp 1 + 3 + 16) * δ ^ 3 / uR ^ 4
        = (Real.exp 1 + 3 + 16) * (δ ^ 3 / uR ^ 4) := by ring
    _ ≤ fragPermLocalConstant * (δ ^ 3 / uR ^ 4) := by
      unfold fragPermLocalConstant
      exact mul_le_mul_of_nonneg_right hconst hnonneg
    _ = fragPermLocalConstant *
        (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) := by
      simp [δ, uR]
