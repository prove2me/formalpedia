-- Prove2me | solution 1 for Erdos146.BinaryPairKernel.conditionalEntropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:03:14.807399+00:00
-- url     : https://prove2.me/submissions/ae4227d1-1e91-445c-817e-25eec23a2608

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Theorems.Thm_Erdos146_BinaryPairKernel_averageDisagreement_eq_four_outcomes
import Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_eq_four_outcomes
import Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_le_one
import Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_nonneg
import Theorems.Thm_Erdos146_binaryEntropy_continuous
import Theorems.Thm_Erdos146_binaryPinskerGap_hasDerivAt
import Theorems.Thm_Erdos146_sqrt_three_mul_entropyTangentRho

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem binaryPinskerGap_continuous : Continuous binaryPinskerGap := by
  unfold binaryPinskerGap
  fun_prop

theorem binaryPinskerGapDeriv_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGapDeriv (binaryPinskerGapDerivTwo q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hcomplement : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have hcomplement_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hqone.symm
  have hderiv :=
    ((Real.hasDerivAt_log hqzero).sub
      (hcomplement.log hcomplement_ne)).sub (hlinear.const_mul 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGapDeriv, binaryPinskerGapDerivTwo]; ring)

theorem binaryPinskerGapDerivTwo_nonneg {q : ℝ}
    (hqzero : 0 < q) (hqone : q < 1) :
    0 ≤ binaryPinskerGapDerivTwo q := by
  have hcomplement : 0 < 1 - q := sub_pos.mpr hqone
  have hidentity :
      binaryPinskerGapDerivTwo q =
        (2 * q - 1) ^ 2 / (q * (1 - q)) := by
    unfold binaryPinskerGapDerivTwo
    field_simp [hqzero.ne', hcomplement.ne']
    ring
  rw [hidentity]
  exact div_nonneg (sq_nonneg _) (mul_pos hqzero hcomplement).le

theorem binaryPinskerGap_convex :
    ConvexOn ℝ (Set.Icc 0 1) binaryPinskerGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := binaryPinskerGapDeriv)
    (f'' := binaryPinskerGapDerivTwo)
    (convex_Icc (0 : ℝ) 1)
    binaryPinskerGap_continuous.continuousOn ?_ ?_ ?_
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact (binaryPinskerGap_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact
      (binaryPinskerGapDeriv_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact binaryPinskerGapDerivTwo_nonneg hq'.1 hq'.2

@[simp] theorem binaryPinskerGap_half :
    binaryPinskerGap ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGap
  rw [Real.binEntropy_two_inv]
  norm_num

@[simp] theorem binaryPinskerGapDeriv_half :
    binaryPinskerGapDeriv ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGapDeriv
  norm_num

theorem binary_pinsker (q : ℝ) (hqzero : 0 ≤ q) (hqone : q ≤ 1) :
    Real.binEntropy q ≤
      Real.log 2 - (2 * q - 1) ^ 2 / 2 := by
  have habove :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ)⁻¹ ≤ x →
        0 ≤ binaryPinskerGap x := by
    intro x hxzero hxone hxhalf
    by_cases hxeq : x = (2 : ℝ)⁻¹
    · simp [hxeq]
    · have hxstrict : (2 : ℝ)⁻¹ < x :=
        lt_of_le_of_ne hxhalf (Ne.symm hxeq)
      have hmid :
          HasDerivAt binaryPinskerGap 0 ((2 : ℝ)⁻¹) := by
        convert binaryPinskerGap_hasDerivAt
          (q := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1
        exact binaryPinskerGapDeriv_half.symm
      have hslope := binaryPinskerGap_convex.le_slope_of_hasDerivAt
        (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show x ∈ Set.Icc 0 1 from ⟨hxzero, hxone⟩)
        hxstrict hmid
      rw [slope_def_field, binaryPinskerGap_half, sub_zero] at hslope
      rcases (div_nonneg_iff.mp hslope) with hpositive | hnegative
      · exact hpositive.1
      · exfalso
        have hden : 0 < x - (2 : ℝ)⁻¹ := sub_pos.mpr hxstrict
        linarith [hnegative.2]
  by_cases hhalf : (2 : ℝ)⁻¹ ≤ q
  · have hgap := habove q hqzero hqone hhalf
    unfold binaryPinskerGap at hgap
    linarith
  · have hcomplement : (2 : ℝ)⁻¹ ≤ 1 - q := by
      norm_num at hhalf ⊢
      linarith
    have hgap := habove (1 - q) (sub_nonneg.mpr hqone)
      (by linarith) hcomplement
    unfold binaryPinskerGap at hgap
    rw [Real.binEntropy_one_sub] at hgap
    nlinarith

theorem log_le_tangent {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at hlog
  linarith

theorem log_four_thirds_lt_one_third :
    Real.log ((4 : ℝ) / 3) < (1 : ℝ) / 3 := by
  have hlog := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 : ℝ) / 3 ≠ 1 by norm_num)
  norm_num at hlog ⊢
  linarith

theorem sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  have hroot := Real.sqrt_nonneg (1 + x)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x by linarith)
  nlinarith [sq_nonneg x]

theorem normalized_binary_cauchy (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    a * x + b * y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hrad : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hroot := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hsquare := Real.sq_sqrt hrad
  have hidentity :
      (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
        (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  rw [hab, one_mul] at hidentity
  nlinarith [sq_nonneg (a * y - b * x)]

theorem binary_log_sum_bound (probability zeroWeight oneWeight : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hzeroWeight : 0 < zeroWeight)
    (honeWeight : 0 < oneWeight) :
    Real.binEntropy probability +
        (1 - probability) * Real.log zeroWeight +
        probability * Real.log oneWeight ≤
      Real.log (zeroWeight + oneWeight) := by
  by_cases hzero : probability = 0
  · subst probability
    simpa using Real.log_le_log hzeroWeight
      (le_add_of_nonneg_right honeWeight.le)
  by_cases hone : probability = 1
  · subst probability
    simpa using Real.log_le_log honeWeight
      (le_add_of_nonneg_left hzeroWeight.le)
  have hprobability_pos : 0 < probability :=
    lt_of_le_of_ne hprobability_zero (Ne.symm hzero)
  have hcomplement_pos : 0 < 1 - probability :=
    sub_pos.mpr (lt_of_le_of_ne hprobability_one hone)
  have hnormalize :
      (1 - probability) * (zeroWeight / (1 - probability)) +
          probability * (oneWeight / probability) =
        zeroWeight + oneWeight := by
    field_simp [hprobability_pos.ne', hcomplement_pos.ne']
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.2
    (show zeroWeight / (1 - probability) ∈ Set.Ioi (0 : ℝ) from
      div_pos hzeroWeight hcomplement_pos)
    (show oneWeight / probability ∈ Set.Ioi (0 : ℝ) from
      div_pos honeWeight hprobability_pos)
    hcomplement_pos.le hprobability_pos.le
    (show (1 - probability) + probability = 1 by ring)
  simp only [smul_eq_mul] at hjensen
  rw [hnormalize] at hjensen
  rw [Real.log_div hzeroWeight.ne' hcomplement_pos.ne',
    Real.log_div honeWeight.ne' hprobability_pos.ne'] at hjensen
  have hentropy :
      Real.binEntropy probability =
        -(1 - probability) * Real.log (1 - probability) -
          probability * Real.log probability := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  rw [hentropy]
  linarith

theorem entropyTangentSigma_pos : 0 < entropyTangentSigma := by
  unfold entropyTangentSigma
  positivity

theorem entropyTangentRho_pos : 0 < entropyTangentRho := by
  unfold entropyTangentRho
  positivity

theorem log_entropyTangentSigma :
    Real.log entropyTangentSigma =
      (3 / 2 : ℝ) * Real.log 2 - Real.log 3 := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold entropyTangentSigma
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), hlogfour]
  ring

theorem log_entropyTangentRho :
    Real.log entropyTangentRho =
      (Real.log 2 - Real.log 3) / 2 := by
  unfold entropyTangentRho
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)]
  ring

theorem entropyTangentZeroCoefficient_eq (q : ℝ) :
    (1 - q) ^ 2 / entropyTangentSigma +
        q ^ 2 / (3 * entropyTangentSigma) +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentZeroCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentZeroCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem entropyTangentOneCoefficient_eq (q : ℝ) :
    (1 - q) ^ 2 / (3 * entropyTangentSigma) +
        q ^ 2 / entropyTangentSigma +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentOneCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentOneCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem entropyTangentCoefficient_norm (q : ℝ) :
    entropyTangentZeroCoefficient q ^ 2 +
        entropyTangentOneCoefficient q ^ 2 =
      1 + (2 * q - 1) ^ 2 / 4 := by
  unfold entropyTangentZeroCoefficient entropyTangentOneCoefficient
  calc
    (Real.sqrt 2 * (3 - 2 * q) / 4) ^ 2 +
        (Real.sqrt 2 * (1 + 2 * q) / 4) ^ 2 =
      (Real.sqrt 2) ^ 2 *
        (((3 - 2 * q) ^ 2 + (1 + 2 * q) ^ 2) / 16) := by ring
    _ = 1 + (2 * q - 1) ^ 2 / 4 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring

theorem entropyTangentLog_constant (q : ℝ) :
    ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
        2 * q * (1 - q) * Real.log entropyTangentRho =
      Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [log_entropyTangentSigma, log_entropyTangentRho,
    Real.log_div (by positivity) (by positivity), hlogfour]
  ring

theorem binaryConditionalLogPotential_tangent_bound
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      Real.binEntropy q / 2 +
        Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) +
        Real.sqrt (1 + (2 * q - 1) ^ 2 / 4) - 1 := by
  have hsum : 0 < zeroAmplitude + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargzero : 0 < zeroAmplitude + oneAmplitude / 3 := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargone : 0 < zeroAmplitude / 3 + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hargmixed :
      0 < (zeroAmplitude + oneAmplitude) / Real.sqrt 3 :=
    div_pos hsum hthree
  have htangentzero := mul_le_mul_of_nonneg_left
    (log_le_tangent hargzero entropyTangentSigma_pos)
    (sq_nonneg (1 - q))
  have htangentone := mul_le_mul_of_nonneg_left
    (log_le_tangent hargone entropyTangentSigma_pos)
    (sq_nonneg q)
  have hmixedweight : 0 ≤ 2 * q * (1 - q) := by
    have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
    positivity
  have htangentmixed := mul_le_mul_of_nonneg_left
    (log_le_tangent hargmixed entropyTangentRho_pos)
    hmixedweight
  have hcombined :=
    add_le_add (add_le_add htangentzero htangentone) htangentmixed
  have hright :
      ((1 - q) ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude + oneAmplitude / 3) /
              entropyTangentSigma - 1) +
        q ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude / 3 + oneAmplitude) /
              entropyTangentSigma - 1)) +
        (2 * q * (1 - q)) *
          (Real.log entropyTangentRho +
            ((zeroAmplitude + oneAmplitude) / Real.sqrt 3) /
              entropyTangentRho - 1) =
        ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
          2 * q * (1 - q) * Real.log entropyTangentRho +
          zeroAmplitude * entropyTangentZeroCoefficient q +
          oneAmplitude * entropyTangentOneCoefficient q - 1 := by
    rw [← entropyTangentZeroCoefficient_eq,
      ← entropyTangentOneCoefficient_eq]
    field_simp [entropyTangentSigma_pos.ne',
      entropyTangentRho_pos.ne', hthree.ne']
    ring
  rw [hright, entropyTangentLog_constant] at hcombined
  have hcauchy := normalized_binary_cauchy
    zeroAmplitude oneAmplitude
    (entropyTangentZeroCoefficient q)
    (entropyTangentOneCoefficient q) hamplitudes
  rw [entropyTangentCoefficient_norm] at hcauchy
  unfold binaryConditionalLogPotential
  linarith

theorem binaryConditionalLogPotential_le_kappa
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      kappa * Real.log 2 := by
  have htangent := binaryConditionalLogPotential_tangent_bound
    q zeroAmplitude oneAmplitude hqzero hqone
    hzeroAmplitude honeAmplitude hamplitudes
  have hpinsker := binary_pinsker q hqzero hqone
  have hsqrt := sqrt_one_add_le ((2 * q - 1) ^ 2 / 4)
    (by positivity)
  have hlogscaled := mul_le_mul_of_nonneg_left
    log_four_thirds_lt_one_third.le
    (show 0 ≤ (2 * q - 1) ^ 2 / 4 by positivity)
  have hkappa :
      kappa * Real.log 2 =
        (3 / 2 : ℝ) * Real.log 2 -
          (3 / 4 : ℝ) * Real.log 3 := by
    unfold kappa logTwo
    field_simp [log_two_pos.ne']
  rw [hkappa]
  nlinarith [sq_nonneg (2 * q - 1)]

end

namespace BinaryPairKernel
section
open Filter Finset SimpleGraph
open scoped Topology

theorem conditionalEntropy_mul_log_two (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy * Real.log 2 =
      (1 - kernel.parentProbability) ^ 2 *
          Real.binEntropy (kernel.childProbability false false) +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          Real.binEntropy (kernel.childProbability false true) +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          Real.binEntropy (kernel.childProbability true false) +
        kernel.parentProbability ^ 2 *
          Real.binEntropy (kernel.childProbability true true) := by
  simp [conditionalEntropy, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass, binaryEntropy]
  field_simp [log_two_pos.ne']
  ring

theorem smoothed_childMarginal (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  rw [childMarginal_eq_four_outcomes,
    childMarginal_eq_four_outcomes kernel]
  simp [smoothed]
  ring

theorem smoothed_averageDisagreement (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  rw [averageDisagreement_eq_four_outcomes,
    averageDisagreement_eq_four_outcomes kernel]
  simp [smoothed]
  ring

theorem smoothedConditionalEntropy_continuous (kernel : BinaryPairKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop

theorem smoothed_conditionalEntropy (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := by
  rfl

theorem conditionalEntropy_logsum_reduction (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy * Real.log 2 -
        Real.binEntropy kernel.childMarginal / 2 -
        Real.log 3 * kernel.averageDisagreement ≤
      binaryConditionalLogPotential kernel.parentProbability
          (Real.sqrt (1 - kernel.childMarginal))
          (Real.sqrt kernel.childMarginal) -
        Real.binEntropy kernel.parentProbability / 2 := by
  let q : ℝ := kernel.parentProbability
  let v : ℝ := kernel.childMarginal
  let a : ℝ := Real.sqrt (1 - v)
  let b : ℝ := Real.sqrt v
  let z₀₀ : ℝ := kernel.childProbability false false
  let z₀₁ : ℝ := kernel.childProbability false true
  let z₁₀ : ℝ := kernel.childProbability true false
  let z₁₁ : ℝ := kernel.childProbability true true
  have hqzero : 0 ≤ q := kernel.parentProbability_nonneg
  have hqone : q ≤ 1 := kernel.parentProbability_le_one
  have hvzero : 0 < v := hmarginal_zero
  have hvone : v < 1 := hmarginal_one
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hvone)
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.mpr hvzero
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have h₀₀ := binary_log_sum_bound z₀₀ a (b / 3)
    (kernel.childProbability_nonneg false false)
    (kernel.childProbability_le_one false false)
    ha (by positivity)
  have h₀₁ := binary_log_sum_bound z₀₁
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg false true)
    (kernel.childProbability_le_one false true)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₀ := binary_log_sum_bound z₁₀
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg true false)
    (kernel.childProbability_le_one true false)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₁ := binary_log_sum_bound z₁₁ (a / 3) b
    (kernel.childProbability_nonneg true true)
    (kernel.childProbability_le_one true true)
    (by positivity) hb
  have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
  have hscaled₀₀ := mul_le_mul_of_nonneg_left h₀₀
    (sq_nonneg (1 - q))
  have hscaled₀₁ := mul_le_mul_of_nonneg_left h₀₁
    (mul_nonneg hcomplement hqzero)
  have hscaled₁₀ := mul_le_mul_of_nonneg_left h₁₀
    (mul_nonneg hqzero hcomplement)
  have hscaled₁₁ := mul_le_mul_of_nonneg_left h₁₁ (sq_nonneg q)
  have hcombined := add_le_add
    (add_le_add (add_le_add hscaled₀₀ hscaled₀₁) hscaled₁₀)
    hscaled₁₁
  have hmarginal :
      v =
        (1 - q) ^ 2 * z₀₀ +
          (1 - q) * q * z₀₁ +
          q * (1 - q) * z₁₀ +
          q ^ 2 * z₁₁ := by
    simpa [q, v, z₀₀, z₀₁, z₁₀, z₁₁] using
      childMarginal_eq_four_outcomes kernel
  have hentropy :
      kernel.conditionalEntropy * Real.log 2 =
        (1 - q) ^ 2 * Real.binEntropy z₀₀ +
          (1 - q) * q * Real.binEntropy z₀₁ +
          q * (1 - q) * Real.binEntropy z₁₀ +
          q ^ 2 * Real.binEntropy z₁₁ := by
    simpa [q, z₀₀, z₀₁, z₁₀, z₁₁] using
      conditionalEntropy_mul_log_two kernel
  have hdisagreement :
      kernel.averageDisagreement =
        (1 - q) ^ 2 * z₀₀ +
          q * (1 - q) + q ^ 2 * (1 - z₁₁) := by
    simpa [q, z₀₀, z₁₁] using
      averageDisagreement_eq_four_outcomes kernel
  have hloga : Real.log a = Real.log (1 - v) / 2 := by
    dsimp [a]
    exact Real.log_sqrt (sub_pos.mpr hvone).le
  have hlogb : Real.log b = Real.log v / 2 := by
    dsimp [b]
    exact Real.log_sqrt hvzero.le
  have hlogthree :
      Real.log (Real.sqrt (3 : ℝ)) = Real.log 3 / 2 :=
    Real.log_sqrt (by positivity)
  have hchildentropy :
      Real.binEntropy v =
        -v * Real.log v - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hleft :
      (((1 - q) ^ 2 *
          (Real.binEntropy z₀₀ +
            (1 - z₀₀) * Real.log a + z₀₀ * Real.log (b / 3)) +
        ((1 - q) * q) *
          (Real.binEntropy z₀₁ +
            (1 - z₀₁) * Real.log (a / Real.sqrt 3) +
              z₀₁ * Real.log (b / Real.sqrt 3))) +
        (q * (1 - q)) *
          (Real.binEntropy z₁₀ +
            (1 - z₁₀) * Real.log (a / Real.sqrt 3) +
              z₁₀ * Real.log (b / Real.sqrt 3))) +
        q ^ 2 *
          (Real.binEntropy z₁₁ +
            (1 - z₁₁) * Real.log (a / 3) + z₁₁ * Real.log b) =
        kernel.conditionalEntropy * Real.log 2 -
          Real.binEntropy v / 2 -
          Real.log 3 * kernel.averageDisagreement := by
    rw [hentropy, hdisagreement, hchildentropy,
      Real.log_div hb.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div ha.ne' hthree.ne',
      Real.log_div hb.ne' hthree.ne',
      Real.log_div ha.ne' (by norm_num : (3 : ℝ) ≠ 0),
      hloga, hlogb, hlogthree]
    linear_combination
      ((Real.log (1 - v) - Real.log v) / 2) * hmarginal
  have hright :
      (((1 - q) ^ 2 * Real.log (a + b / 3) +
        ((1 - q) * q) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        (q * (1 - q)) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        q ^ 2 * Real.log (a / 3 + b) =
        binaryConditionalLogPotential q a b - Real.binEntropy q / 2 := by
    have hmixed :
        a / Real.sqrt 3 + b / Real.sqrt 3 =
          (a + b) / Real.sqrt 3 := by ring
    rw [hmixed]
    unfold binaryConditionalLogPotential
    ring
  rw [hleft, hright] at hcombined
  simpa [q, v, a, b] using hcombined

theorem conditionalEntropy_bound_of_marginal_interior
    (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hzeroAmplitude :
      0 ≤ Real.sqrt (1 - kernel.childMarginal) :=
    Real.sqrt_nonneg _
  have honeAmplitude : 0 ≤ Real.sqrt kernel.childMarginal :=
    Real.sqrt_nonneg _
  have hamplitudes :
      Real.sqrt (1 - kernel.childMarginal) ^ 2 +
          Real.sqrt kernel.childMarginal ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_pos.mpr hmarginal_one).le,
      Real.sq_sqrt hmarginal_zero.le]
    ring
  have hpotential := binaryConditionalLogPotential_le_kappa
    kernel.parentProbability
    (Real.sqrt (1 - kernel.childMarginal))
    (Real.sqrt kernel.childMarginal)
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hzeroAmplitude honeAmplitude hamplitudes
  have hreduction := conditionalEntropy_logsum_reduction kernel
    hmarginal_zero hmarginal_one
  have hright :
      (kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        kappa * Real.log 2 +
          Real.log 3 * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy logTwo
    field_simp [log_two_pos.ne']
  have hscaled :
      kernel.conditionalEntropy * Real.log 2 ≤
        (kappa + logTwo 3 * kernel.averageDisagreement +
          (binaryEntropy kernel.childMarginal -
            binaryEntropy kernel.parentProbability) / 2) * Real.log 2 := by
    rw [hright]
    linarith
  exact (mul_le_mul_iff_of_pos_right log_two_pos).mp hscaled

end
end BinaryPairKernel

end Erdos146

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by
    dsimp [mixing]
    positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryPairKernel := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto :
      Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have hnonnegative := mul_nonneg
      (sub_nonneg.mpr (hmixing_le_one n))
      (childMarginal_nonneg kernel)
    have hpositive := div_pos (hmixing_pos n) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmarginal_one (n : ℕ) : (approximation n).childMarginal < 1 := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal < 1
    rw [hformula]
    have hproduct := mul_le_mul_of_nonneg_left
      (childMarginal_le_one kernel)
      (sub_nonneg.mpr (hmixing_le_one n))
    have hpositive := hmixing_pos n
    nlinarith
  have hconditional_tendsto :
      Filter.Tendsto (fun n => (approximation n).conditionalEntropy)
        Filter.atTop (nhds kernel.conditionalEntropy) := by
    have hcontinuous :=
      (smoothedConditionalEntropy_continuous kernel).continuousAt.tendsto.comp
        hmixing_tendsto
    have hzero :
        smoothedConditionalEntropy kernel 0 = kernel.conditionalEntropy := by
      simp [smoothedConditionalEntropy, conditionalEntropy]
    rw [hzero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with n
    exact (smoothed_conditionalEntropy kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)).symm
  have hmarginal_tendsto :
      Filter.Tendsto (fun n => (approximation n).childMarginal)
        Filter.atTop (nhds kernel.childMarginal) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.childMarginal))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.childMarginal + mixing n / 2)
          Filter.atTop (nhds kernel.childMarginal) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hdisagreement_tendsto :
      Filter.Tendsto (fun n => (approximation n).averageDisagreement)
        Filter.atTop (nhds kernel.averageDisagreement) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.averageDisagreement))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.averageDisagreement + mixing n / 2)
          Filter.atTop (nhds kernel.averageDisagreement) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_averageDisagreement kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := by
    rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          kappa + logTwo 3 * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          (kappa + logTwo 3 * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hdisagreement_term :=
      (tendsto_const_nhds (x := logTwo 3)).mul hdisagreement_tendsto
    have hentropy_term :=
      (hchildentropy_tendsto.sub
        (tendsto_const_nhds (x :=
          binaryEntropy kernel.parentProbability))).div_const 2
    have hsum :=
      (tendsto_const_nhds (x := kappa)).add
        (hdisagreement_term.add hentropy_term)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto'
    hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior
    (approximation n) (hmarginal_zero n) (hmarginal_one n)
