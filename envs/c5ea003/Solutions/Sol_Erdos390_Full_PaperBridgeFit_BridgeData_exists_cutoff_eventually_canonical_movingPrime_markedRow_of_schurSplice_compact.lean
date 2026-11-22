-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:16:26.496988+00:00
-- url     : https://prove2.me/submissions/e4b151c6-d653-490d-af70-4d0ae6dcd3b2

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Definitions.Def_erdos390_analytic_nonstep_certificate
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualBandSchur_fastGauge_eq_projectedTarget
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualSquarefreeMarkedRow_sub_reference_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_actualWeightedRow_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_nuisanceResidual_bandRegression_markedRow_le_of_profiles
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_referenceMarkedRow_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_slow_div_mul_actualTwoStageCompensatedVariance
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_vectorFieldProfilesMarkedConstant_le_majorant
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_diagonal_sub_reference_le
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles




section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := @Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
end
section
universe u_1 u_3
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles : Erdos390.RemainingAnalyticGoal001_010.{u_1, u_3} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_actualWeightedRow : Erdos390.RemainingAnalyticGoal001_006.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_actualWeightedRow_compact
end
/- Source module: Erdos390.Full.RegularRelativeMesh -/
section


/-!
# Existence of a finite regular relative mesh

Section 8.4 partitions the positive logarithmic interval `[delta,1]` into
geometric cells.  This file constructs such a mesh rather than leaving its
existence as a certificate.  Given `0 < delta < 1` and a requested upper
relative width `eta > 0`, the number of cells is the ceiling of the relevant
logarithmic ratio and the common relative width is adjusted so that the last
endpoint is exactly `1`.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)













theorem endpoint_succ (k : ℕ) :
    M.endpoint (k + 1) = M.endpoint k * (1 + M.ratio) := by
  unfold endpoint
  rw [pow_succ]
  ring



theorem endpoint_pos (hdelta : 0 < delta) (k : ℕ) :
    0 < M.endpoint k := by
  unfold endpoint
  exact mul_pos hdelta (pow_pos (by linarith [M.ratio_pos]) k)

theorem lower_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.lower k := M.endpoint_pos hdelta k.1

theorem width_eq_ratio_mul_lower (k : Fin M.cellCount) :
    M.width k = M.ratio * M.lower k := by
  unfold width upper lower
  rw [M.endpoint_succ]
  ring

theorem width_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.width k := by
  rw [M.width_eq_ratio_mul_lower]
  exact mul_pos M.ratio_pos (M.lower_pos hdelta k)

theorem lower_lt_upper (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k < M.upper k := by
  rw [← sub_pos, ← width]
  exact M.width_pos hdelta k



theorem upper_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k ≤ 1 := by
  have hpow : (1 + M.ratio) ^ (k.1 + 1) ≤
      (1 + M.ratio) ^ M.cellCount :=
    pow_le_pow_right₀ (by linarith [M.ratio_pos]) (Nat.succ_le_iff.mpr k.2)
  unfold upper endpoint
  calc
    delta * (1 + M.ratio) ^ (k.1 + 1) ≤
        delta * (1 + M.ratio) ^ M.cellCount :=
      mul_le_mul_of_nonneg_left hpow hdelta.le
    _ = 1 := M.lastEndpoint



/-- The positive cells telescope exactly from `delta` to `1`. -/
theorem sum_width_eq_one_sub_delta :
    ∑ k : Fin M.cellCount, M.width k = 1 - delta := by
  change (∑ k : Fin M.cellCount,
      (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
    1 - delta
  calc
    (∑ k : Fin M.cellCount,
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) k.1) =
        ∑ k ∈ Finset.range M.cellCount,
          (M.endpoint (k + 1) - M.endpoint k) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ M.endpoint (i + 1) - M.endpoint i) M.cellCount
    _ = 1 - delta := by
      rw [Finset.sum_range_sub, M.endpoint_cellCount, M.endpoint_zero]

end Mesh



end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

































/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]













theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring



theorem covariance_smul_left (mu : FiniteProbability Omega)
    (a : ℝ) (F G : Omega → ℝ) :
    mu.covariance (fun omega ↦ a * F omega) G =
      a * mu.covariance F G := by
  unfold covariance
  rw [mu.expect_smul a F]
  rw [show (fun omega ↦ a * F omega * G omega) =
      fun omega ↦ a * (F omega * G omega) by
    funext omega
    ring]
  rw [mu.expect_smul]
  ring



theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]

theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale



















private theorem primeBand_subset_primesUpTo (n W : ℕ) :
    primeBand n W ⊆ primesUpTo (yNat n) := by
  intro p hp
  have h := mem_primeBand.mp hp
  simp [primesUpTo, h.1, h.2.2]

















private theorem integral_one_div_mul_log {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, 1 / (t * Real.log t)) =
      Real.log (Real.log Y) - Real.log (Real.log 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume 2 Y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog0))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  rw [Set.uIcc_of_le hY] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog0 : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have hd := (Real.hasDerivAt_log ht0).log hlog0
  convert hd using 1
  field_simp

/-- An explicit Mertens-type upper bound, obtained from the global Chebyshev
bound by Abel summation.  It is sufficient for every harmonic loss in
Lemma 7.5 and does not invoke the prime number theorem as an assumption. -/
theorem fullReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullReciprocalSum Y ≤
      2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
  rw [fullReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogYhalf : (1 / 2 : ℝ) ≤ Real.log (Y : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) hYR
    nlinarith [Real.log_two_gt_d9]
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hboundary :
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
        2 * Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
          (Real.log 4 * (Y : ℝ)) /
            ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 2 * Real.log 4 := by
        field_simp [hY0.ne', hlogY0.ne']
        nlinarith
  have hint :
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
        3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
          ∫ t in (2 : ℝ)..Y,
            3 * Real.log 4 * (1 / (t * Real.log t)) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_mertensIntegrand hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have hlog0 : Real.log t ≠ 0 :=
            Real.log_ne_zero_of_pos_of_ne_one
              (by linarith [ht.1]) (by linarith [ht.1])
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (continuousAt_const.div
                (continuousAt_id.mul (Real.continuousAt_log ht0))
                (mul_ne_zero ht0 hlog0)))
        · intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
            have hmono : Real.log 2 ≤ Real.log t :=
              Real.log_le_log (by norm_num) ht.1
            nlinarith [Real.log_two_gt_d9]
          calc
            Chebyshev.theta t * (Real.log t + 1) /
                (t ^ 2 * Real.log t ^ 2) ≤
                (Real.log 4 * t) * (Real.log t + 1) /
                  (t ^ 2 * Real.log t ^ 2) := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
            _ ≤ 3 * Real.log 4 * (1 / (t * Real.log t)) := by
              field_simp [ht0.ne', (show Real.log t ≠ 0 by linarith)]
              nlinarith
      _ = 3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_mul_log hYR]
  linarith

/-- A global Chebyshev bound for the logarithmically weighted reciprocal
prime sum.  The deliberately simple constant is uniform in the endpoint. -/
theorem fullLogReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullLogReciprocalSum Y ≤ Real.log 4 * (1 + Real.log (Y : ℝ)) := by
  rw [fullLogReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤ Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤
          (Real.log 4 * (Y : ℝ)) / (Y : ℝ) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by field_simp
  have hint :
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
        Real.log 4 * Real.log (Y : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
          ∫ t in (2 : ℝ)..Y, Real.log 4 * (1 / t) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_theta_div_sq hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id ht0))
        · intro t ht
          calc
            Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
            _ = Real.log 4 * (1 / t) := by
              have ht0 : t ≠ 0 := by linarith [ht.1]
              field_simp
      _ = Real.log 4 * Real.log ((Y : ℝ) / 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos (by norm_num) hY0]
      _ ≤ Real.log 4 * Real.log (Y : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlog4
        apply Real.log_le_log (div_pos hY0 (by norm_num))
        linarith
  nlinarith

theorem bandLogReciprocalSum_le_full (n W : ℕ) :
    bandLogReciprocalSum n W ≤ fullLogReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  have hp' : p ≤ yNat n ∧ p.Prime := by
    simpa [primesUpTo] using hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.2.one_le)) (by positivity)

theorem bandReciprocalSum_le_full (n W : ℕ) :
    bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  positivity

/-- The unweighted prime harmonic mass has precisely the `O(log L)` loss
allowed in Lemma 7.5.  The constant is explicit and independent of `W` and of
every later tilt box. -/
theorem eventually_bandReciprocalSum_le_logL (W : ℕ) :
    ∀ᶠ n in atTop,
      bandReciprocalSum n W ≤ 12 * Real.log (L n) := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLTop : Tendsto (fun n : ℕ => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hlog4nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4upper : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvLog2 : (Real.log 2)⁻¹ ≤ 2 := by
    rw [← one_div, one_div_le hlog2pos (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hloglog2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    calc
      (-1 : ℝ) ≤ 1 - (Real.log 2)⁻¹ := by linarith
      _ ≤ Real.log (Real.log 2) := Real.one_sub_inv_le_log_of_pos hlog2pos
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogLTop.eventually (eventually_ge_atTop (5 : ℝ))] with n hn hyn hLn hlogLn
  have hyNat : 2 ≤ yNat n := Nat.le_floor hyn
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hlogNatPos : 0 < Real.log (yNat n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogNatLeY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogNatLeL : Real.log (yNat n : ℝ) ≤ L n := by
    calc
      Real.log (yNat n : ℝ) ≤ Real.log (y n) := hlogNatLeY
      _ = (2 / 9 : ℝ) * L n := log_y hn
      _ ≤ L n := by nlinarith
  have hloglogNatLeL :
      Real.log (Real.log (yNat n : ℝ)) ≤ Real.log (L n) :=
    Real.log_le_log hlogNatPos hlogNatLeL
  have hraw :
      bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
    calc
      bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) :=
        bandReciprocalSum_le_full n W
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (Real.log (yNat n : ℝ)) - Real.log (Real.log 2)) :=
        fullReciprocalSum_le (yNat n) hyNat
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
        gcongr
  calc
    bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := hraw
    _ = Real.log 4 *
        (2 + 3 * Real.log (L n) - 3 * Real.log (Real.log 2)) := by ring
    _ ≤ Real.log 4 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_left _ hlog4nonneg
      nlinarith
    _ ≤ 3 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_right hlog4upper
      nlinarith
    _ ≤ 12 * Real.log (L n) := by nlinarith

private theorem bandTReciprocalSum_eq (n W : ℕ) :
    bandTReciprocalSum n W =
      bandLogReciprocalSum n W / Real.log (y n) := by
  rw [bandTReciprocalSum, bandLogReciprocalSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [tPrime]
  ring

/-- The `t_p/p` mass of the moving prime band is uniformly bounded.  This is
the first-moment estimate used in the weighted covariance-row contraction. -/
theorem eventually_bandTReciprocalSum_le (W : ℕ) :
    ∀ᶠ n in atTop, bandTReciprocalSum n W ≤ 2 * Real.log 4 := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (9 / 2 : ℝ))] with n hn hyn hLn
  have hyNat : 2 ≤ yNat n := by
    exact Nat.le_floor hyn
  have hlogy : 1 ≤ Real.log (y n) := by
    rw [log_y hn]
    nlinarith
  have hlogy0 : 0 < Real.log (y n) := lt_of_lt_of_le (by norm_num) hlogy
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogFloor : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hnum :
      Real.log 4 * (1 + Real.log (yNat n : ℝ)) ≤
        Real.log 4 * (2 * Real.log (y n)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
    nlinarith
  calc
    bandTReciprocalSum n W =
        bandLogReciprocalSum n W / Real.log (y n) := bandTReciprocalSum_eq n W
    _ ≤ fullLogReciprocalSum (yNat n) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right (bandLogReciprocalSum_le_full n W)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (1 + Real.log (yNat n : ℝ))) /
          Real.log (y n) := by
      exact div_le_div_of_nonneg_right (fullLogReciprocalSum_le (yNat n) hyNat)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (2 * Real.log (y n))) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hlogy0)
    _ = 2 * Real.log 4 := by field_simp

end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section























theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity



















end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Proposition87 -/
section


/-!
# The finite and ODE algebra behind Proposition 8.7

The analytic inputs to the nonlinear fit (uniform covariance gaps, relative row
errors, and existence of an integral curve inside the preselected box) are kept as
explicit hypotheses.  This file proves the block solve, the slow-coordinate and
effective-velocity ledgers, compatibility recovery, and the straight-target chain
rule with no hidden limiting assertion.
-/

open Metric Set

namespace Erdos390

section BlockInverse

variable {Q : Type*} [AddCommGroup Q] [Module ℝ Q]









end BlockInverse

section SlowCoordinateBounds





/-- A `w`-sized compensated coefficient multiplied by the `1/w` slow velocity
gives a box-independent contribution to every prime row. -/
theorem effective_prime_velocity_bound
    (base coeff lambda w Cbase Ccoeff Cslow : ℝ)
    (hw : 0 < w) (hCslow : 0 ≤ Cslow)
    (hbase : |base| ≤ Cbase)
    (hcoeff : |coeff| ≤ Ccoeff * w)
    (hlambda : |lambda| ≤ Cslow / w) :
    |base + lambda * coeff| ≤ Cbase + Cslow * Ccoeff := by
  have hquot : 0 ≤ Cslow / w := div_nonneg hCslow (le_of_lt hw)
  have hmul : |lambda| * |coeff| ≤ (Cslow / w) * (Ccoeff * w) :=
    mul_le_mul hlambda hcoeff (abs_nonneg coeff) hquot
  calc
    |base + lambda * coeff| ≤ |base| + |lambda * coeff| := abs_add_le _ _
    _ = |base| + |lambda| * |coeff| := by rw [abs_mul]
    _ ≤ Cbase + (Cslow / w) * (Ccoeff * w) := add_le_add hbase hmul
    _ = Cbase + Cslow * Ccoeff := by field_simp

end SlowCoordinateBounds

section GaugeAnnihilator

variable {E : Type*} [AddCommGroup E] [Module ℝ E]





end GaugeAnnihilator

section PrechosenBox

variable {E : Type*} [PseudoMetricSpace E]



end PrechosenBox

section StraightTarget

variable {E Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]











end StraightTarget

end Erdos390

end

/- Source module: Erdos390.Full.NonlinearFitODE -/
section


/-!
# The finite nonlinear moment lift

This file turns the scalar covariance--Jacobian identity for a finite
exponential family into the vector Jacobian used by the nonlinear fitting
argument.  A quantitative covariance gap is then used to construct the
inverse Jacobian (rather than assuming a right inverse), define the actual
ODE vector field, and prove its exact solve and velocity estimates.

The final section records a non-circular continuation theorem.  Its input is
an explicit covariance gap on a ball chosen before solving the ODE; local
Lipschitz continuity is derived from the finite exponential formulas and
operator inversion.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section



namespace VectorExponentialFamily

variable {Omega E : Type*} [Fintype Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]





































theorem jacobian_isInvertible [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    (vf.jacobian xi).IsInvertible := by
  exact ⟨vf.jacobianEquiv hgamma hgap, rfl⟩



theorem jacobian_vectorField [CompleteSpace E]
    (vf : VectorExponentialFamily Omega E) (target : E)
    {gamma : ℝ} (hgamma : 0 < gamma) {xi : E}
    (hgap : vf.HasCovarianceGap gamma xi) :
    vf.jacobian xi (vf.vectorField target xi) = target := by
  exact (vf.jacobian_isInvertible hgamma hgap).self_apply_inverse target



/-! ## Smoothness and non-circular continuation -/



















end VectorExponentialFamily

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]



































end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















































































/-! ### Exact main/nuisance coordinate splitting -/





















































theorem inner_mainEmbed_combine (u v : B.MainSpace)
    (z : B.NuisanceSpace) :
    inner ℝ (B.mainEmbed u) (B.combine v z) = inner ℝ u v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ c : B.Coord, B.combine v z c * B.mainEmbed u c) =
    ∑ c : MainCoord B.GaugeIndex, v c * u c
  rw [B.sum_coord_split]
  have hmain : (∑ c : MainCoord B.GaugeIndex,
      B.combine v z (match c with
        | .gauge j => .gauge j
        | .slow => .slow) *
      B.mainEmbed u (match c with
        | .gauge j => .gauge j
        | .slow => .slow)) = ∑ c, v c * u c := by
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  have hnuisance : (∑ c : NuisanceCoord B.HeadIndex,
      B.combine v z (match c with
        | .physical => .physical
        | .head h => .head h) *
      B.mainEmbed u (match c with
        | .physical => .physical
        | .head h => .head h)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    cases c <;> simp
  erw [hmain, hnuisance, add_zero]















/-- Bilinear covariance--Jacobian identity for the concrete vector family. -/
theorem inner_jacobian [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.vectorFamily.jacobian xi y) =
      (B.q / B.L) * B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  let F : B.sampleData.Sample → ℝ :=
    fun m => inner ℝ x (B.statistic m)
  have hleft : HasFDerivAt
      (fun eta => inner ℝ x (B.vectorFamily.vectorMoment eta))
      (((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi)) xi := by
    exact ((innerSL ℝ) x).hasFDerivAt.comp xi
      (B.vectorFamily.hasFDerivAt_vectorMoment xi)
  have hright : HasFDerivAt
      (B.vectorFamily.scalarFamily.moment F)
      ((B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi) xi :=
    B.vectorFamily.scalarFamily.hasFDerivAt_moment_covariance F xi
  have hfun : (fun eta => inner ℝ x
      (B.vectorFamily.vectorMoment eta)) =
      B.vectorFamily.scalarFamily.moment F := by
    funext eta
    exact B.vectorFamily.inner_vectorMoment x eta
  have hmaps : ((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi) =
      (B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi :=
    hleft.unique (hfun ▸ hright)
  have happ := congrArg
    (fun T : B.ParamSpace →L[ℝ] ℝ => T y) hmaps
  change inner ℝ x (B.vectorFamily.jacobian xi y) =
    (B.vectorFamily.baseMass / B.vectorFamily.scale) *
      B.vectorFamily.scalarFamily.covarianceScore F xi y at happ
  rw [B.vectorFamily.scalarFamily.covarianceScore_apply F xi y] at happ
  have hscore :
      (fun m => B.vectorFamily.scalarFamily.score m y) =
        fun m => inner ℝ y (B.statistic m) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hscore, B.vectorFamily_baseMass] at happ
  simpa only [vectorFamily] using happ

theorem inner_covarianceOperator [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    B.inner_jacobian]
  field_simp [ne_of_gt B.L_pos, ne_of_gt B.q_pos]





















theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]













theorem exactNuisanceRegression_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.nuisanceCovarianceOperator xi
        (B.exactNuisanceRegression xi hgamma hgap u) =
      B.crossCovarianceOperator xi u := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _





















/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperPrimePowerRow -/
section


/-!
# The paper prime-band row contraction

This module specializes the actual finite-law contraction to

* the literal band `primeBand n W`,
* `t_p = log p / log y`,
* reciprocal weight `u_p = 1 / p`,
* row normalization `p`, and
* `invW = 1 / W`.

Thus every elementary prime-coordinate and prime-sum input in the final row
step of paper Lemma 7.5 is discharged here.  The remaining hypotheses are
exactly the actual `JI`, `IJ`, `JJ`, diagonal, and endpoint estimates proved
by the marked four-chamber analysis.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRow

open ArithmeticModel Scale PrimeSums
open PrimePowerCovariance PrimePowerRowTransfer

noncomputable section

lemma tPrime_nonneg_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    0 <= tPrime n p := by
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    nlinarith
  have hlogp : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
  exact div_nonneg hlogp hlogy.le

lemma tPrime_le_one_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    tPrime n p <= 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y hn0]
    nlinarith
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hyfloor : (yNat n : Real) <= y n :=
    Nat.floor_le (le_of_lt (y_pos hn0))
  have hpcast : (p : Real) <= y n := by
    exact (by exact_mod_cast le_yNat_of_mem_primeBand hp :
      (p : Real) <= (yNat n : Real)).trans hyfloor
  have hlog : Real.log (p : Real) <= Real.log (y n) :=
    Real.log_le_log hp0 hpcast
  unfold tPrime
  calc
    Real.log (p : Real) / Real.log (y n) <=
        Real.log (y n) / Real.log (y n) :=
      div_le_div_of_nonneg_right hlog hlogy.le
    _ = 1 := div_self hlogy.ne'





namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000



end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow

end

/- Source module: Erdos390.Full.RegularMeshPrimeCutoffsEventually -/
section


/-!
# Eventual population of every explicit regular-mesh prime cell

For a fixed regular mesh, each positive logarithmic cell has fixed positive
width.  Its multiplicative size on the original prime scale therefore tends
to infinity.  This file proves the scale-separation hypotheses used by the
Bertrand construction automatically for all sufficiently large `n`, and
hence produces the arithmetic partition and interval certificate without a
mesh or prime-existence assumption.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel RegularRelativeMesh PositiveCellTransfer

theorem tendsto_y_atTop :
    Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
  unfold y
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
    tendsto_natCast_atTop_atTop

/-- Every fixed positive logarithmic coordinate tends to infinity on the
original prime scale. -/
theorem tendsto_scalePoint_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ scalePoint n t) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ ↦ (y n) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_y_atTop
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  unfold scalePoint
  rw [Real.rpow_def_of_pos (Scale.y_pos hn)]
  congr 1
  ring



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)









end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PartitionPrimeDeviationGeometry -/
section


/-!
# Prime-deviation moments for an actual arithmetic partition

This is the sample-independent form of the arithmetic geometry in Lemma
8.6.  It works directly with `ArithmeticBandGeometry.Partition`, so the
regular mesh constructed from explicit natural endpoints can be audited
without first manufacturing the smooth-number probability space.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PositiveCellTransfer
open KernelPrimeQuadrature PrimeCoordinateSecondMoment

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : ArithmeticBandGeometry.Partition n W Band)











theorem totalL1_eq_sum_bandL1 : P.totalL1 = ∑ j : Band, P.bandL1 j := by
  unfold totalL1 bandL1
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦ (1 / (p.1 : ℝ)) * |P.deviation p|)]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

theorem variance_eq_sum_bandVariance :
    P.variance = ∑ j : Band, P.bandVariance j := by
  change (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p) = _
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p)]
  apply Finset.sum_congr rfl
  intro j hj
  unfold bandVariance deviation
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Erdos390.Lemma84.WeightedBandData.cellDeviation]
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) *
        (P.center (P.band p) - tPrime n p.1) =
    (1 / (p.1 : ℝ)) * (P.center (P.band p) - tPrime n p.1) ^ 2
  rw [pow_two]
  ring

theorem bandVariance_eq_second_sub_mass_center_sq (j : Band) :
    P.bandVariance j =
      P.bandSecondMoment j - P.mass j * P.center j ^ 2 := by
  have hrewrite : P.bandVariance j =
      ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) *
        (P.center j - tPrime n p.1) ^ 2 := by
    unfold bandVariance deviation
    apply Finset.sum_congr rfl
    intro p hp
    have hpj : P.band p = j :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
    rw [hpj]
  rw [hrewrite]
  have hmass : (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = P.mass j := rfl
  have hfirst :
      (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) = P.mass j * P.center j := by
    change (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) =
      P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * (P.center j - tPrime n p.1) ^ 2) =
        ∑ p ∈ P.data.fiber j,
          ((1 / (p.1 : ℝ)) * P.center j ^ 2 -
            2 * P.center j * ((1 / (p.1 : ℝ)) * tPrime n p.1) +
            (1 / (p.1 : ℝ)) * tPrime n p.1 ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) * P.center j ^ 2 -
        2 * P.center j *
          (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1) +
        ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1 ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
    _ = P.bandSecondMoment j - P.mass j * P.center j ^ 2 := by
      rw [hmass, hfirst]
      unfold bandSecondMoment
      ring







theorem center_mem_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.center j ∈ Set.Icc a b := by
  have hH := P.data.mass_pos j
  have hLower : a * P.mass j ≤
      ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change a * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (hcoord p hp).1 (by positivity : 0 ≤ 1 / (p.1 : ℝ))
  have hUpper :
      (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1) ≤
        P.mass j * b := by
    change _ ≤ (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) * b
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hcoord p hp).2 (by positivity)
  change ((∑ p ∈ P.data.fiber j,
    (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass j) ∈ Set.Icc a b
  exact ⟨(le_div_iff₀ hH).2 hLower,
    (div_le_iff₀ hH).2 (by simpa only [mul_comm] using hUpper)⟩

theorem abs_deviation_le_width_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b)
    (p : BandPrime n W) (hp : p ∈ P.data.fiber j) :
    |P.deviation p| ≤ b - a := by
  have hpj : P.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
  have hc := P.center_mem_of_coord_bounds j hcoord
  unfold deviation
  rw [hpj, abs_le]
  constructor <;> linarith [(hcoord p hp).1, (hcoord p hp).2, hc.1, hc.2]

theorem bandL1_le_width_mul_mass_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.bandL1 j ≤ (b - a) * P.mass j := by
  unfold bandL1
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * |P.deviation p|) ≤
    (b - a) * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have hdev := P.abs_deviation_le_width_of_coord_bounds j hcoord p hp
  calc
    (1 / (p.1 : ℝ)) * |P.deviation p| ≤
        (1 / (p.1 : ℝ)) * (b - a) :=
      mul_le_mul_of_nonneg_left hdev hw
    _ = (b - a) * (1 / (p.1 : ℝ)) := by ring

theorem bandVariance_le_width_sq_mul_mass_of_coord_bounds
    (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.bandVariance j ≤ (b - a) ^ 2 * P.mass j := by
  unfold bandVariance
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * P.deviation p ^ 2) ≤
    (b - a) ^ 2 * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hdev := P.abs_deviation_le_width_of_coord_bounds j hcoord p hp
  have hwidth : 0 ≤ b - a := (abs_nonneg _).trans hdev
  have hsq : P.deviation p ^ 2 ≤ (b - a) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hwidth] using hdev)
  calc
    (1 / (p.1 : ℝ)) * P.deviation p ^ 2 ≤
        (1 / (p.1 : ℝ)) * (b - a) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (b - a) ^ 2 * (1 / (p.1 : ℝ)) := by ring

theorem bandL1_le_two_mass_mul_center (j : Band)
    (hcoordNonneg : ∀ p ∈ P.data.fiber j, 0 ≤ tPrime n p.1) :
    P.bandL1 j ≤ 2 * P.mass j * P.center j := by
  have hc0 : 0 ≤ P.center j := by
    change 0 ≤ (∑ q ∈ P.data.fiber j,
      (1 / (q.1 : ℝ)) * tPrime n q.1) / P.mass j
    exact div_nonneg (Finset.sum_nonneg fun q hq ↦
      mul_nonneg (by positivity) (hcoordNonneg q hq)) (P.data.mass_pos j).le
  have hfirst :
      (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) = P.mass j * P.center j := by
    change (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) =
      P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
    field_simp [ne_of_gt (P.data.mass_pos j)]
  have hmass : (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = P.mass j := rfl
  unfold bandL1
  calc
    (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * |P.deviation p|) ≤
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * (P.center j + tPrime n p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpj : P.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      rw [deviation, hpj]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.2
        ⟨by linarith [hcoordNonneg p hp], by linarith [hcoordNonneg p hp]⟩)
        (by positivity)
    _ = 2 * P.mass j * P.center j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, hfirst]
      ring

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.MovingLowMomentQuadrature -/
section


/-!
# Endpoint-uniform first logarithmic prime moment

For the moving low cell the lower cutoff is fixed while the upper endpoint
grows.  Keeping the integrable `1/(x log^3 x)` PNT majorant, rather than
freezing `log x` at the lower endpoint, gives an error independent of the
upper endpoint.  Division by the ambient logarithmic scale therefore tends
to zero and supplies the relative low-center transfer.
-/

open Set

noncomputable section

namespace Erdos390.Full.MovingLowMomentQuadrature

open MeasureTheory PrimeSums PrimeBandQuadrature



























theorem fullLogReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullLogReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * fullLogReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 +
        fullLogReciprocalSumUniformConstant /
          (2 * Real.log (A : ℝ) ^ 2) :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullLogReciprocalSum_interval_uniform_error_bound).2)
    A Y hA hAY



end Erdos390.Full.MovingLowMomentQuadrature

end

/- Source module: Erdos390.Full.RegularMeshMomentBounds -/
section


/-!
# Moment budgets for the regular relative mesh

This is the elementary continuum census behind the arithmetic estimates in
Lemma 8.6.  The moving-low cell provides the quadratic lower bound, while the
geometric positive cells have total `L¹` cost at most their common relative
width and total quadratic cost at most its square.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)







theorem upper_div_lower_eq_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k / M.lower k = 1 + M.ratio := by
  rw [show M.upper k = M.lower k * (1 + M.ratio) by
    unfold upper lower
    exact M.endpoint_succ k.1]
  field_simp [ne_of_gt (M.lower_pos hdelta k)]

theorem cellHarmonicMass_eq_log_one_add_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k = Real.log (1 + M.ratio) := by
  unfold cellHarmonicMass
  rw [M.upper_div_lower_eq_one_add_ratio hdelta k]



theorem cellHarmonicMass_le_ratio
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.cellHarmonicMass k ≤ M.ratio := by
  rw [M.cellHarmonicMass_eq_log_one_add_ratio hdelta k]
  have h := Real.log_le_sub_one_of_pos (by linarith [M.ratio_pos] :
    0 < 1 + M.ratio)
  linarith

theorem lower_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k ≤ 1 :=
  (M.lower_lt_upper hdelta k).le.trans (M.upper_le_one hdelta k)

theorem width_le_ratio (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.width k ≤ M.ratio := by
  rw [M.width_eq_ratio_mul_lower]
  nlinarith [M.ratio_pos, M.lower_pos hdelta k,
    M.lower_le_one hdelta k]









end Mesh





















end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBounds -/
section


/-!
# Actual arithmetic `L¹` and variance bounds for the regular mesh

The endpoints in this file are the explicit floored endpoints from
`RegularMeshPrimeCutoffs`, and every sum is over the actual primes.  The
first part proves the finite deterministic assembly.  The final part derives
its moment inputs from the proved PNT quadratures.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor

theorem y_gt_one {n : ℕ} (hn : 1 < n) : 1 < y n := by
  have hlog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  exact (Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le).mp hlog

theorem realLogCoordinate_scalePoint {n : ℕ} (hn : 1 < n) (t : ℝ) :
    realLogCoordinate (y n) (scalePoint n t) = t := by
  have hlog : Real.log (y n) ≠ 0 := ne_of_gt (Real.log_pos (y_gt_one hn))
  unfold realLogCoordinate scalePoint
  rw [Real.log_exp]
  field_simp [hlog]

theorem realLogCoordinate_floorScale_lt_prime
    {n p : ℕ} (hn : 1 < n) {t : ℝ}
    (hp : ⌊scalePoint n t⌋₊ < p) :
    t < tPrime n p := by
  have hscale : 0 ≤ scalePoint n t := (Real.exp_pos _).le
  have hreal : scalePoint n t < (p : ℝ) :=
    (Nat.floor_lt hscale).mp hp
  have hpPos : 0 < (p : ℝ) := (Real.exp_pos _).trans hreal
  have hlog := Real.strictMonoOn_log
    (show scalePoint n t ∈ Set.Ioi 0 from Real.exp_pos _)
    (show (p : ℝ) ∈ Set.Ioi 0 from hpPos) hreal
  have hlogy := Real.log_pos (y_gt_one hn)
  unfold tPrime
  rw [← realLogCoordinate_scalePoint hn t]
  unfold realLogCoordinate
  exact (div_lt_div_iff_of_pos_right hlogy).2 hlog

theorem prime_logCoordinate_le_of_le_floorScale
    {n p : ℕ} (hn : 1 < n) {t : ℝ}
    (hpPos : 0 < p) (hp : p ≤ ⌊scalePoint n t⌋₊) :
    tPrime n p ≤ t := by
  have hfloorLe : (⌊scalePoint n t⌋₊ : ℝ) ≤ scalePoint n t :=
    Nat.floor_le (Real.exp_pos _).le
  have hpCast : (p : ℝ) ≤ (⌊scalePoint n t⌋₊ : ℝ) := by
    exact_mod_cast hp
  have hpReal : (p : ℝ) ≤ scalePoint n t := hpCast.trans hfloorLe
  have hpRealPos : 0 < (p : ℝ) := by exact_mod_cast hpPos
  have hlog := Real.log_le_log hpRealPos hpReal
  have hlogy := Real.log_pos (y_gt_one hn)
  unfold tPrime
  rw [← realLogCoordinate_scalePoint hn t]
  unfold realLogCoordinate
  exact div_le_div_of_nonneg_right hlog hlogy.le

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)
  {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper

omit hLower in
/-- Every actual prime in the low fiber lies in `[0,delta]`. -/
theorem low_coord_bounds (hn : 1 < n)
    (p : BandPrime n W) (hp : p ∈ P.data.fiber (0 : Fin (M.cellCount + 1))) :
    tPrime n p.1 ∈ Set.Icc 0 delta := by
  have hpBand : P.band p = (0 : Fin (M.cellCount + 1)) :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
  have hpInterval :=
    (PositiveCellTransfer.IntervalCertificate.band_eq_iff E p 0).mp hpBand
  have hpUpper := hpInterval.2
  rw [hUpper 0] at hpUpper
  have hendpoint : M.endpoint 0 = delta := M.endpoint_zero
  simp only [Fin.val_zero, fullCutoff, hendpoint] at hpUpper
  constructor
  · have hpPrime := prime_of_mem_primeBand p.2
    unfold tPrime
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le))
      (Real.log_pos (y_gt_one hn)).le
  · exact prime_logCoordinate_le_of_le_floorScale hn
      (prime_of_mem_primeBand p.2).pos hpUpper

/-- Every actual prime in positive cell `k` lies in the intended continuum
cell, despite the use of floored natural endpoints. -/
theorem positive_coord_bounds (hn : 1 < n) (k : Fin M.cellCount)
    (p : BandPrime n W)
    (hp : p ∈ P.data.fiber k.succ) :
    tPrime n p.1 ∈ Set.Icc (M.lower k) (M.upper k) := by
  have hpBand : P.band p = k.succ :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
  have hpInterval :=
    (PositiveCellTransfer.IntervalCertificate.band_eq_iff E p k.succ).mp hpBand
  have hpLower := hpInterval.1
  have hpUpper := hpInterval.2
  rw [hLower k.succ] at hpLower
  rw [hUpper k.succ] at hpUpper
  have hsuccVal : k.succ.1 = k.1 + 1 := rfl
  simp only [hsuccVal, fullCutoff] at hpLower
  simp only [fullCutoff] at hpUpper
  exact ⟨(realLogCoordinate_floorScale_lt_prime hn hpLower).le,
    prime_logCoordinate_le_of_le_floorScale hn
      (prime_of_mem_primeBand p.2).pos hpUpper⟩



/-- The first-moment part of the finite assembly is uniform for an
arbitrary relative-mesh upper parameter `eta`.  Unlike the variance lower
bound, it does not require `M.ratio ≤ delta`. -/
theorem actual_L1_bound_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    P.totalL1 ≤ 7 * (delta + M.ratio) := by
  have hrho0 := M.ratio_pos.le
  have hlowCoord := low_coord_bounds M P E hUpper hn
  have hposCoord := positive_coord_bounds M P E hLower hUpper hn
  have hlowL1 := P.bandL1_le_two_mass_mul_center 0
    (fun p hp ↦ (hlowCoord p hp).1)
  have hposL1 (k : Fin M.cellCount) :
      P.bandL1 k.succ ≤ 3 * M.ratio * M.width k := by
    have hraw := P.bandL1_le_width_mul_mass_of_coord_bounds k.succ
      (hposCoord k)
    rw [show M.upper k - M.lower k = M.width k by rfl] at hraw
    calc
      P.bandL1 k.succ ≤ M.width k * P.mass k.succ := hraw
      _ ≤ M.width k * (3 * M.ratio) :=
        mul_le_mul_of_nonneg_left (R.positiveMass k)
          (M.width_pos hdelta k).le
      _ = 3 * M.ratio * M.width k := by ring
  rw [P.totalL1_eq_sum_bandL1, Fin.sum_univ_succ]
  calc
    P.bandL1 0 + ∑ k : Fin M.cellCount, P.bandL1 k.succ ≤
        4 * delta + ∑ k : Fin M.cellCount,
          3 * M.ratio * M.width k := by
      apply add_le_add
      · exact hlowL1.trans (by linarith [R.lowFirst])
      · exact Finset.sum_le_sum fun k hk ↦ hposL1 k
    _ = 4 * delta + 3 * M.ratio * (1 - delta) := by
      rw [← Finset.mul_sum, M.sum_width_eq_one_sub_delta]
    _ ≤ 7 * (delta + M.ratio) := by nlinarith

omit hLower in
/-- The moving low cell contributes a fixed multiple of `delta²` without
any comparison between the positive mesh ratio and `delta`. -/
theorem actual_low_bandVariance_lower_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    delta ^ 2 / 4 ≤ P.bandVariance 0 := by
  have hlowCoord := low_coord_bounds M P E hUpper hn
  have hlowCenterNonneg : 0 ≤ P.center 0 :=
    (P.center_mem_of_coord_bounds 0 hlowCoord).1
  have hlowFirstNonneg : 0 ≤ P.mass 0 * P.center 0 :=
    mul_nonneg (P.data.mass_pos 0).le hlowCenterNonneg
  have hcenterTerm : P.mass 0 * P.center 0 ^ 2 ≤ delta ^ 2 / 12 := by
    have hmassPos := P.data.mass_pos 0
    have hidentity : P.mass 0 * P.center 0 ^ 2 =
        (P.mass 0 * P.center 0) ^ 2 / P.mass 0 := by
      field_simp [ne_of_gt hmassPos]
    rw [hidentity, div_le_iff₀ hmassPos]
    have hfirstSq : (P.mass 0 * P.center 0) ^ 2 ≤ (2 * delta) ^ 2 :=
      (sq_le_sq₀ hlowFirstNonneg (by positivity)).2 R.lowFirst
    have hright : (2 * delta) ^ 2 ≤ delta ^ 2 / 12 * P.mass 0 := by
      nlinarith [R.lowMass, sq_nonneg delta]
    exact hfirstSq.trans hright
  rw [P.bandVariance_eq_second_sub_mass_center_sq]
  linarith [R.lowSecondLower, hcenterTerm]

/-- The quadratic upper bound is uniform for independent mesh parameters;
it does not use `M.ratio ≤ delta`. -/
theorem actual_variance_upper_of_ready
    (hdelta : 0 < delta) (hn : 1 < n)
    (R : MomentReady M P) :
    P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  have hposCoord := positive_coord_bounds M P E hLower hUpper hn
  have hlowVarUpper : P.bandVariance 0 ≤ delta ^ 2 := by
    rw [P.bandVariance_eq_second_sub_mass_center_sq]
    have hterm : 0 ≤ P.mass 0 * P.center 0 ^ 2 :=
      mul_nonneg (P.data.mass_pos 0).le (sq_nonneg _)
    linarith [R.lowSecondUpper]
  have hposVar (k : Fin M.cellCount) :
      P.bandVariance k.succ ≤ 3 * M.ratio * M.width k ^ 2 := by
    have hraw := P.bandVariance_le_width_sq_mul_mass_of_coord_bounds k.succ
      (hposCoord k)
    rw [show M.upper k - M.lower k = M.width k by rfl] at hraw
    calc
      P.bandVariance k.succ ≤ M.width k ^ 2 * P.mass k.succ := hraw
      _ ≤ M.width k ^ 2 * (3 * M.ratio) :=
        mul_le_mul_of_nonneg_left (R.positiveMass k) (sq_nonneg _)
      _ = 3 * M.ratio * M.width k ^ 2 := by ring
  have hsumWidthSq :
      (∑ k : Fin M.cellCount, M.width k ^ 2) ≤ M.ratio := by
    calc
      (∑ k : Fin M.cellCount, M.width k ^ 2) ≤
          ∑ k : Fin M.cellCount, M.ratio * M.width k := by
        apply Finset.sum_le_sum
        intro k hk
        have hw0 := (M.width_pos hdelta k).le
        have hwle := M.width_le_ratio hdelta k
        nlinarith
      _ = M.ratio * (1 - delta) := by
        rw [← Finset.mul_sum, M.sum_width_eq_one_sub_delta]
      _ ≤ M.ratio := by nlinarith [M.ratio_pos]
  rw [P.variance_eq_sum_bandVariance, Fin.sum_univ_succ]
  calc
    P.bandVariance 0 + ∑ k : Fin M.cellCount, P.bandVariance k.succ ≤
        delta ^ 2 + ∑ k : Fin M.cellCount,
          3 * M.ratio * M.width k ^ 2 := by
      exact add_le_add hlowVarUpper
        (Finset.sum_le_sum fun k hk ↦ hposVar k)
    _ = delta ^ 2 + 3 * M.ratio *
        (∑ k : Fin M.cellCount, M.width k ^ 2) := by
      rw [← Finset.mul_sum]
    _ ≤ delta ^ 2 + 3 * M.ratio ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsumWidthSq
        (show 0 ≤ 3 * M.ratio by
          exact mul_nonneg (by norm_num) M.ratio_pos.le)
      nlinarith
    _ ≤ 4 * (delta + M.ratio) ^ 2 := by
      nlinarith [M.ratio_pos, hdelta]



end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointAnchorCoverage -/
section


/-!
# Uniform interior anchor coverage for the endpoint mesh

Flooring a power-scale endpoint changes its logarithmic coordinate by at
most `log 2 / log y` once the endpoint is at least two.  This proves that a
fixed strictly interior regular-mesh cell remains interior in the actual
endpoint mesh and retains at least half of its continuum length.
-/

open Filter Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature
open ContinuumCellGraph

theorem floor_scalePoint_coordinate_bounds
    {n : ℕ} (hn : 1 < n) {t : ℝ}
    (hxTwo : 2 ≤ scalePoint n t) :
    t - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ∧
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ≤ t := by
  let x := scalePoint n t
  let m := ⌊x⌋₊
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hxpos : 0 < x := by unfold x scalePoint; positivity
  have hmUpper : (m : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hfloorLt : x < (m : ℝ) + 1 := by
    simpa only [m] using Nat.lt_floor_add_one x
  have hmLower : x / 2 ≤ (m : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) :=
    (div_pos hxpos (by norm_num)).trans_le hmLower
  have hlogLower : Real.log (x / 2) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (div_pos hxpos (by norm_num)) hmLower
  have hlogUpper : Real.log (m : ℝ) ≤ Real.log x :=
    Real.log_le_log hmpos hmUpper
  have hlogX : Real.log x = t * Real.log (y n) := by
    unfold x scalePoint
    rw [Real.log_exp]
  have hlogDiv : Real.log (x / 2) = Real.log x - Real.log 2 := by
    rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  constructor
  · unfold realLogCoordinate
    apply (le_div_iff₀ hylog).2
    have hscaled :
        (t - Real.log 2 / Real.log (y n)) * Real.log (y n) =
          Real.log x - Real.log 2 := by
      rw [sub_mul, div_mul_cancel₀ _ hylog.ne', hlogX]
    rw [hscaled, ← hlogDiv]
    exact hlogLower
  · unfold realLogCoordinate
    apply (div_le_iff₀ hylog).2
    rw [hlogX] at hlogUpper
    exact hlogUpper

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)







end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBoundsEventually -/
section


/-!
# Eventual actual-prime moment bounds on the canonical regular mesh

This file discharges the `MomentReady` inputs of
`RegularMeshActualMomentBounds` from the unconditional prime number theorem
quadratures.  The endpoint family is the canonical family of floored powers
of `y`; no continuum mesh, prime-population, or moment estimate is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem tendsto_log_y_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (y n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_y_atTop

theorem tendsto_fixed_cutoffCoordinate_zero (W : ℕ) :
    Tendsto (fun n : ℕ ↦ realLogCoordinate (y n) (W : ℝ))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto (fun _n : ℕ ↦ Real.log (W : ℝ)) atTop
      (nhds (Real.log (W : ℝ))) := tendsto_const_nhds
  simpa only [realLogCoordinate, div_eq_mul_inv, mul_zero] using
    hConst.mul hInv

theorem tendsto_floor_scalePoint_coordinate
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ))
      atTop (nhds t) := by
  have hLoss : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_y_atTop
  have hLowerT : Tendsto
      (fun n : ℕ ↦ t - Real.log 2 / Real.log (y n))
      atTop (nhds t) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hLoss
  have hUpperT : Tendsto (fun _n : ℕ ↦ t) atTop (nhds t) :=
    tendsto_const_nhds
  have hTwo := (tendsto_scalePoint_atTop ht).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hLower : ∀ᶠ n : ℕ in atTop,
      t - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) := by
    filter_upwards [eventually_gt_atTop 1, hTwo] with n hn hnTwo
    exact (floor_scalePoint_coordinate_bounds hn hnTwo).1
  have hUpper : ∀ᶠ n : ℕ in atTop,
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ≤ t := by
    filter_upwards [eventually_gt_atTop 1, hTwo] with n hn hnTwo
    exact (floor_scalePoint_coordinate_bounds hn hnTwo).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLowerT hUpperT hLower hUpper

theorem tendsto_positive_lowerCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
  simpa only [cutoffCoordinate, fullCutoff_succ,
    RegularRelativeMesh.Mesh.lower] using
      tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)

theorem tendsto_positive_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  simpa only [cutoffCoordinate, show k.1 + 2 = (k.1 + 1) + 1 by omega,
    fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
      tendsto_floor_scalePoint_coordinate hUpperPos

theorem tendsto_low_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W 1)
      atTop (nhds delta) := by
  simpa only [cutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
    tendsto_floor_scalePoint_coordinate hdelta







theorem tendsto_positiveContinuumMass
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ positiveContinuumMass M n W k) atTop
      (nhds (M.cellHarmonicMass k)) := by
  have hLower := tendsto_positive_lowerCoordinate M hdelta W k
  have hUpper := tendsto_positive_upperCoordinate M hdelta W k
  have hLogLower : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 1)))
      atTop (nhds (Real.log (M.lower k))) :=
    (Real.continuousAt_log (ne_of_gt (M.lower_pos hdelta k))).tendsto.comp
      hLower
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  have hLogUpper : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 2)))
      atTop (nhds (Real.log (M.upper k))) :=
    (Real.continuousAt_log (ne_of_gt hUpperPos)).tendsto.comp hUpper
  have hDiff := hLogUpper.sub hLogLower
  simpa only [positiveContinuumMass,
    RegularRelativeMesh.Mesh.cellHarmonicMass,
    Real.log_div (ne_of_gt hUpperPos)
      (ne_of_gt (M.lower_pos hdelta k))] using hDiff

theorem tendsto_lowFirstContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowFirstContinuum M n W)
      atTop (nhds delta) := by
  simpa only [lowFirstContinuum, sub_zero] using
    (tendsto_low_upperCoordinate M hdelta W).sub
      (tendsto_fixed_cutoffCoordinate_zero W)

theorem tendsto_lowSecondContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowSecondContinuum M n W)
      atTop (nhds (delta ^ 2 / 2)) := by
  have hUpper := (tendsto_low_upperCoordinate M hdelta W).pow 2
  have hLower := (tendsto_fixed_cutoffCoordinate_zero W).pow 2
  have hDiff := hUpper.sub hLower
  have hDiv := hDiff.div_const (2 : ℝ)
  simpa only [lowSecondContinuum, zero_pow (by omega : 2 ≠ 0), sub_zero]
    using hDiv

theorem tendsto_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))

theorem tendsto_positive_massError_zero
    (hdelta : 0 < delta) (W : ℕ) (C : ℝ)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      5 * C / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3)
      atTop (nhds 0) := by
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_positive_lowerCutoff_atTop M hdelta W k)
  have hLog : Tendsto
      (fun n : ℕ ↦ Real.log (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp hCutReal
  have hInv : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLog
  have hConst : Tendsto (fun _n : ℕ ↦ 5 * C) atTop (nhds (5 * C)) :=
    tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 3)
  simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_pow (by omega : 3 ≠ 0)]
    using hMain

theorem tendsto_lowFirstError_zero (C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      (2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n))
      atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_log_y_atTop

theorem tendsto_lowSecondError_zero
    (C : ℝ) {W : ℕ} (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      3 * C / (Real.log (y n) ^ 2 * Real.log (W : ℝ)))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto
      (fun _n : ℕ ↦ 3 * C / Real.log (W : ℝ)) atTop
      (nhds (3 * C / Real.log (W : ℝ))) := tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 2)
  have hMainZero : Tendsto (fun n : ℕ ↦
      (3 * C / Real.log (W : ℝ)) * (Real.log (y n))⁻¹ ^ 2)
      atTop (nhds 0) := by simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  have hLogW : Real.log (W : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hW))
  field_simp [hLogW]

theorem tendsto_lowHarmonicMain_atTop
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
        Real.log (Real.log (W : ℝ))) atTop atTop := by
  have hCutNat : Tendsto (fun n : ℕ ↦ fullCutoff M n W 1)
      atTop atTop := by
    simpa only [fullCutoff_succ, M.endpoint_zero] using
      tendsto_nat_floor_atTop.comp (tendsto_scalePoint_atTop hdelta)
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hCutNat
  have hLogLog := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp hCutReal)
  rw [tendsto_atTop]
  intro b
  have hEvent := hLogLog.eventually
    (eventually_ge_atTop (b + Real.log (Real.log (W : ℝ))))
  filter_upwards [hEvent] with n hn
  change b + Real.log (Real.log (W : ℝ)) ≤
    Real.log (Real.log (fullCutoff M n W 1 : ℝ)) at hn
  linarith



theorem eventually_endpointMomentBounds
    (hdelta : 0 < delta) (W : ℕ) (Cmass Cfirst Csecond : ℝ)
    (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      EndpointMomentBounds M n W Cmass Cfirst Csecond := by
  have hPositiveMain : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        positiveContinuumMass M n W k ≤ 2 * M.ratio := by
    rw [Filter.eventually_all]
    intro k
    have hT := tendsto_positiveContinuumMass M hdelta W k
    have hLimit : M.cellHarmonicMass k < 2 * M.ratio :=
      (M.cellHarmonicMass_le_ratio hdelta k).trans_lt (by
        linarith [M.ratio_pos])
    exact hT.eventually (eventually_le_nhds hLimit)
  have hPositiveError : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        5 * Cmass / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 ≤
          M.ratio := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_massError_zero M hdelta W Cmass k).eventually
      (eventually_le_nhds M.ratio_pos)
  have hFirstMain : ∀ᶠ n : ℕ in atTop,
      lowFirstContinuum M n W ≤ 3 * delta / 2 := by
    have hLimit : delta < 3 * delta / 2 := by linarith
    exact (tendsto_lowFirstContinuum M hdelta W).eventually
      (eventually_le_nhds hLimit)
  have hFirstError : ∀ᶠ n : ℕ in atTop,
      (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
        Cfirst / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n) ≤
          delta / 2 := by
    exact (tendsto_lowFirstError_zero Cfirst W).eventually
      (eventually_le_nhds (by linarith : (0 : ℝ) < delta / 2))
  have hSecondLower : ∀ᶠ n : ℕ in atTop,
      5 * delta ^ 2 / 12 ≤ lowSecondContinuum M n W := by
    have hStrict : 5 * delta ^ 2 / 12 < delta ^ 2 / 2 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_ge_nhds hStrict)
  have hSecondUpper : ∀ᶠ n : ℕ in atTop,
      lowSecondContinuum M n W ≤ 11 * delta ^ 2 / 12 := by
    have hStrict : delta ^ 2 / 2 < 11 * delta ^ 2 / 12 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_le_nhds hStrict)
  have hSecondError : ∀ᶠ n : ℕ in atTop,
      3 * Csecond / (Real.log (y n) ^ 2 * Real.log (W : ℝ)) ≤
        delta ^ 2 / 12 := by
    have hStrict : (0 : ℝ) < delta ^ 2 / 12 := by positivity
    exact (tendsto_lowSecondError_zero Csecond hW).eventually
      (eventually_le_nhds hStrict)
  have hLowMass : ∀ᶠ n : ℕ in atTop,
      48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
        Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
          Real.log (Real.log (W : ℝ)) :=
    (tendsto_lowHarmonicMain_atTop M hdelta W).eventually
      (eventually_ge_atTop
        (48 + 5 * Cmass / Real.log (W : ℝ) ^ 3))
  filter_upwards [eventually_gt_atTop 1, hPositiveMain, hPositiveError,
    hFirstMain, hFirstError, hSecondLower, hSecondUpper, hSecondError,
    hLowMass] with n hn hPM hPE hFM hFE hSL hSU hSE hLM
  exact ⟨hn, hPM, hPE, hFM, hFE, hSL, hSU, hSE, hLM⟩

variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper



/-- The actual prime-deviation coefficient is uniformly of size at most
`w = delta + ratio`; this is the pointwise input to the compensated-score
regression ledger. -/
theorem actual_deviation_sup_le_scale
    (hdelta : 0 < delta) (hn : 1 < n)
    (p : BandPrime n W) :
    |P.deviation p| ≤ delta + M.ratio := by
  let motive := fun j : Fin (M.cellCount + 1) ↦
    P.band p = j → |P.deviation p| ≤ delta + M.ratio
  apply (Fin.cases (motive := motive) ?_ ?_
    (P.band p)) rfl
  · intro hpBand
    have hpFiber : p ∈ P.data.fiber (0 : Fin (M.cellCount + 1)) :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mpr hpBand
    have hdev := P.abs_deviation_le_width_of_coord_bounds 0
      (low_coord_bounds M P E hUpper hn) p hpFiber
    nlinarith [M.ratio_pos]
  · intro k hpBand
    have hpFiber : p ∈ P.data.fiber k.succ :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mpr hpBand
    have hdev := P.abs_deviation_le_width_of_coord_bounds k.succ
      (positive_coord_bounds M P E hLower hUpper hn k) p hpFiber
    rw [show M.upper k - M.lower k = M.width k by rfl] at hdev
    have hw := M.width_le_ratio hdelta k
    nlinarith







end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperWeightedInverseExport -/
section


/-!
# Export of the sharp inverse in the paper's weighted band norm

The finite graph argument is naturally written after the diagonal change of
variables `b j = alpha j * q j`.  This file records the change of variables
as an exact linear equivalence between the two arithmetic gauges.  It also
proves that the projected raw row-normalized matrix is conjugate to
`projectedSharpLinearMap`.  Consequently an inverse estimate in the ordinary
supremum norm of `q` is literally the paper estimate
`max_j |b_j| / |alpha_j|` for the unscaled band coefficient `b`.

There is no limiting centre and no continuum gauge in this algebraic export.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open ArithmeticGaugeStableInverse
open CompressedArithmeticOperator
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse
open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band]















theorem paperSharpNorm_eq_piNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) :
    paperSharpNorm H alpha hAlpha b =
      ‖fun j ↦ b.1 j / alpha j‖ := by
  rfl























/-- Coordinate form of the preceding weighted bound. -/
theorem abs_raw_coordinate_le_paperSharpNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) (j : Band) :
    |b.1 j| ≤ |alpha j| * paperSharpNorm H alpha hAlpha b := by
  have hcoord : |b.1 j / alpha j| ≤
      paperSharpNorm H alpha hAlpha b := by
    rw [paperSharpNorm_eq_piNorm]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (fun k ↦ b.1 k / alpha k) j
  have hrewrite : |b.1 j| = |alpha j| * |b.1 j / alpha j| := by
    rw [abs_div]
    field_simp [abs_ne_zero.mpr (hAlpha j)]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hcoord (abs_nonneg (alpha j))

end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.PaperCompensatedCoefficientBounds -/
section


/-!
# Actual compensated-prime coefficient bounds for Lemma 8.6

This file specializes the elementary coefficient ledger to the literal
arithmetic prime partition.  The regression vector is an element of the
paper's exact arithmetic gauge

`sum_j H_j * alpha_j * q_j = 0`,

and the compensated coefficient is literally
`c_p = (alpha_{j(p)} - t_p) - q_{j(p)}`.  Thus none of the three norms below
is represented by an abstract array or stored in a certificate.

The sole regression input is the sharp norm estimate produced by the
weighted inverse and the row estimate.  All remaining estimates are derived
from the actual prime sums and the already proved canonical-mesh moment
bounds.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)













theorem center_mem_zero_one (hn : 1 < n) (j : Band) :
    P.center j ∈ Set.Icc (0 : ℝ) 1 := by
  apply P.center_mem_of_coord_bounds j
  intro p hp
  have hpBand : p.1 ∈ primeBand n W := p.2
  exact ⟨PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn hpBand⟩











/-- Exact first-moment identity for the arithmetic centers. -/
theorem sum_mass_mul_center_eq_bandTReciprocalSum :
    (∑ j : Band, P.mass j * P.center j) =
      bandTReciprocalSum n W := by
  have hcenter (j : Band) :
      P.mass j * P.center j =
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ j : Band, P.mass j * P.center j) =
        ∑ j : Band, ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hcenter j
    _ = ∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            rw [← Finset.sum_fiberwise Finset.univ P.band
              (fun p : BandPrime n W ↦
                (1 / (p.1 : ℝ)) * tPrime n p.1)]
            apply Finset.sum_congr rfl
            intro j hj
            rfl
    _ = bandTReciprocalSum n W := by
          unfold bandTReciprocalSum
          have hattach := Finset.sum_attach (primeBand n W)
            (fun p ↦ tPrime n p / (p : ℝ))
          rw [← hattach]
          apply Finset.sum_congr rfl
          intro p hp
          ring

/-- Exact reindexing of a bandwise coefficient through the actual partition. -/
theorem sum_regressionCoefficient_eq_sum_band
    (q : RawGaugeSpace P.mass P.center)
    (F : ℝ → ℝ) :
    (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * F (P.regressionCoefficient q p)) =
      ∑ j : Band, P.mass j * F (q.1 j) := by
  unfold regressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦ (1 / (p.1 : ℝ)) * F (q.1 (P.band p)))]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * F (q.1 (P.band p))) =
    P.mass j * F (q.1 j)
  calc
    _ = ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * F (q.1 j) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpj : P.band p = j :=
            (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
          rw [hpj]
    _ = P.mass j * F (q.1 j) := by
          rw [← Finset.sum_mul]
          rfl

/-- The literal weighted square of the actual deviation is definitionally
the arithmetic partition variance. -/
theorem deviationL2Sq_eq_variance :
    (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * (P.deviation p) ^ 2) = P.variance := by
  change (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * (P.deviation p) ^ 2) =
    ∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) *
        (P.center (P.band p) - tPrime n p.1)
  rw [pow_two]
  ring

/-- A sharp regression bound gives the literal pointwise band bound. -/
theorem abs_regressionCoefficient_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w : ℝ}
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (p : BandPrime n W) :
    |P.regressionCoefficient q p| ≤ C * w := by
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    P.mass P.center (P.center_ne_zero hn) q (P.band p)
  have hcenter := (P.center_mem_zero_one hn (P.band p)).2
  have hcenter0 := (P.center_mem_zero_one hn (P.band p)).1
  have habsCenter : |P.center (P.band p)| ≤ 1 := by
    rw [abs_of_nonneg hcenter0]
    exact hcenter
  calc
    |P.regressionCoefficient q p| = |q.1 (P.band p)| := rfl
    _ ≤ |P.center (P.band p)| *
        paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
    _ ≤ 1 * paperSharpNorm P.mass P.center (P.center_ne_zero hn) q :=
      mul_le_mul_of_nonneg_right habsCenter (norm_nonneg _)
    _ ≤ C * w := by simpa using hsharp

/-- The actual weighted `L¹` norm of the regression vector. -/
theorem regressionL1_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K) :
    P.regressionL1 q ≤ C * K * w := by
  have hcw : 0 ≤ C * w := mul_nonneg hC hw
  have hsum : P.regressionL1 q ≤
      (C * w) * ∑ j : Band, P.mass j * P.center j := by
    rw [regressionL1, P.sum_regressionCoefficient_eq_sum_band q abs]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      P.mass P.center (P.center_ne_zero hn) q j
    have hcenter0 := (P.center_mem_zero_one hn j).1
    have hq : |q.1 j| ≤ P.center j * (C * w) := by
      calc
        |q.1 j| ≤ |P.center j| *
            paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
        _ ≤ |P.center j| * (C * w) :=
          mul_le_mul_of_nonneg_left hsharp (abs_nonneg _)
        _ = P.center j * (C * w) := by rw [abs_of_nonneg hcenter0]
    calc
      P.mass j * |q.1 j| ≤ P.mass j * (P.center j * (C * w)) :=
        mul_le_mul_of_nonneg_left hq (P.data.mass_pos j).le
      _ = (C * w) * (P.mass j * P.center j) := by ring
  rw [P.sum_mass_mul_center_eq_bandTReciprocalSum] at hsum
  calc
    P.regressionL1 q ≤ (C * w) * bandTReciprocalSum n W := hsum
    _ ≤ (C * w) * K := mul_le_mul_of_nonneg_left hbandT hcw
    _ = C * K * w := by ring

/-- The actual weighted quadratic norm of the regression vector. -/
theorem regressionL2Sq_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K) :
    P.regressionL2Sq q ≤ C ^ 2 * K * w ^ 2 := by
  have hcw : 0 ≤ C * w := mul_nonneg hC hw
  have hsum : P.regressionL2Sq q ≤
      (C * w) ^ 2 * ∑ j : Band, P.mass j * P.center j := by
    rw [regressionL2Sq, P.sum_regressionCoefficient_eq_sum_band q
      (fun x ↦ x ^ 2)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      P.mass P.center (P.center_ne_zero hn) q j
    have hcenter := P.center_mem_zero_one hn j
    have hqabs : |q.1 j| ≤ P.center j * (C * w) := by
      calc
        |q.1 j| ≤ |P.center j| *
            paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
        _ ≤ |P.center j| * (C * w) :=
          mul_le_mul_of_nonneg_left hsharp (abs_nonneg _)
        _ = P.center j * (C * w) := by rw [abs_of_nonneg hcenter.1]
    have hqsq : (q.1 j) ^ 2 ≤ P.center j * (C * w) ^ 2 := by
      have hsq : (q.1 j) ^ 2 ≤ (P.center j * (C * w)) ^ 2 := by
        have hright0 : 0 ≤ P.center j * (C * w) :=
          mul_nonneg hcenter.1 hcw
        have hprod := mul_nonneg (sub_nonneg.mpr hqabs)
          (add_nonneg (abs_nonneg (q.1 j)) hright0)
        rw [← sq_abs (q.1 j)]
        nlinarith
      have hcenterSq : P.center j ^ 2 ≤ P.center j := by
        have hprod := mul_nonneg hcenter.1 (sub_nonneg.mpr hcenter.2)
        nlinarith
      calc
        (q.1 j) ^ 2 ≤ (P.center j * (C * w)) ^ 2 := hsq
        _ = P.center j ^ 2 * (C * w) ^ 2 := by ring
        _ ≤ P.center j * (C * w) ^ 2 :=
          mul_le_mul_of_nonneg_right hcenterSq (sq_nonneg _)
    calc
      P.mass j * (q.1 j) ^ 2 ≤
          P.mass j * (P.center j * (C * w) ^ 2) :=
        mul_le_mul_of_nonneg_left hqsq (P.data.mass_pos j).le
      _ = (C * w) ^ 2 * (P.mass j * P.center j) := by ring
  rw [P.sum_mass_mul_center_eq_bandTReciprocalSum] at hsum
  calc
    P.regressionL2Sq q ≤ (C * w) ^ 2 * bandTReciprocalSum n W := hsum
    _ ≤ (C * w) ^ 2 * K :=
      mul_le_mul_of_nonneg_left hbandT (sq_nonneg _)
    _ = C ^ 2 * K * w ^ 2 := by ring

/-- All three paper coefficient bounds for the literal compensated vector.
The constants are explicit and independent of the number of bands. -/
theorem compensatedCoefficient_three_bounds
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K)
    (hdevSup : ∀ p : BandPrime n W, |P.deviation p| ≤ w)
    (hdevL1 : P.totalL1 ≤ 7 * w)
    (hdevL2 : P.variance ≤ 4 * w ^ 2) :
    (∀ p : BandPrime n W,
        |P.compensatedCoefficient q p| ≤ (1 + C) * w) ∧
      P.compensatedL1 q ≤ (7 + C * K) * w ∧
      P.compensatedL2Sq q ≤
        2 * (4 + C ^ 2 * K) * w ^ 2 := by
  have hqSup : ∀ p : BandPrime n W,
      |P.regressionCoefficient q p| ≤ C * w :=
    P.abs_regressionCoefficient_le hn q hsharp
  have hqL1 : P.regressionL1 q ≤ C * K * w :=
    P.regressionL1_le hn q hC hw hsharp hbandT
  have hqL2 : P.regressionL2Sq q ≤ C ^ 2 * K * w ^ 2 :=
    P.regressionL2Sq_le hn q hC hw hsharp hbandT
  constructor
  · intro p
    unfold compensatedCoefficient
    calc
      |P.deviation p - P.regressionCoefficient q p| ≤
          |P.deviation p| + |P.regressionCoefficient q p| := abs_sub _ _
      _ ≤ w + C * w := add_le_add (hdevSup p) (hqSup p)
      _ = (1 + C) * w := by ring
  constructor
  · unfold compensatedL1
    calc
      (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * |P.compensatedCoefficient q p|) ≤
          ∑ p : BandPrime n W,
            ((1 / (p.1 : ℝ)) * |P.deviation p| +
              (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p|) := by
        apply Finset.sum_le_sum
        intro p hp
        unfold compensatedCoefficient
        simpa only [mul_add] using
          (mul_le_mul_of_nonneg_left (abs_sub
              (P.deviation p) (P.regressionCoefficient q p))
            (one_div_nonneg.mpr
              (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity)))
      _ = (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * |P.deviation p|) +
          ∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p| :=
        Finset.sum_add_distrib
      _ ≤ 7 * w + C * K * w := add_le_add hdevL1 hqL1
      _ = (7 + C * K) * w := by ring
  · unfold compensatedL2Sq
    calc
      (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * (P.compensatedCoefficient q p) ^ 2) ≤
          ∑ p : BandPrime n W,
            (2 * ((1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
              2 * ((1 / (p.1 : ℝ)) *
                (P.regressionCoefficient q p) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hsquare : (P.deviation p - P.regressionCoefficient q p) ^ 2 ≤
            2 * P.deviation p ^ 2 +
              2 * (P.regressionCoefficient q p) ^ 2 := by
          nlinarith [sq_nonneg (P.deviation p + P.regressionCoefficient q p)]
        unfold compensatedCoefficient
        calc
          (1 / (p.1 : ℝ)) *
              (P.deviation p - P.regressionCoefficient q p) ^ 2 ≤
            (1 / (p.1 : ℝ)) *
              (2 * P.deviation p ^ 2 +
                2 * (P.regressionCoefficient q p) ^ 2) :=
              mul_le_mul_of_nonneg_left hsquare
                (one_div_nonneg.mpr
                  (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity))
          _ = 2 * ((1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
              2 * ((1 / (p.1 : ℝ)) *
                (P.regressionCoefficient q p) ^ 2) := by ring
      _ = 2 * (∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
          2 * (∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * (P.regressionCoefficient q p) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * P.variance + 2 * P.regressionL2Sq q := by
        rw [P.deviationL2Sq_eq_variance]
        rfl
      _ ≤ 2 * (4 * w ^ 2) + 2 * (C ^ 2 * K * w ^ 2) := by
        linarith
      _ = 2 * (4 + C ^ 2 * K) * w ^ 2 := by ring

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperActualCompensatedRegression -/
section


/-!
# The actual two-stage compensated regression in Lemma 8.6

The objects in this file live on the genuine guard-deleted, tilted finite
probability space from `PaperBridgeFit`.  In particular, the nuisance
coefficient is not an abstract vector satisfying a normal equation: it is
defined by applying the inverse of the proved actual nuisance covariance
operator to the literal covariance vector of the post-band-regression score.

This file proves the exact finite identities used before the analytic
`w^2` comparison: the prime-coefficient expansion, nuisance normal equation,
orthogonality, Schur variance identity, and marked-row decomposition.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















theorem partition_compensatedCoefficient_eq
    (q : B.RawBandGauge)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.partition.compensatedCoefficient q p =
      B.actualCompensatedCoefficient q p := rfl

/-- Reindexing over the actual partition identifies the raw band score with
the corresponding primewise coefficient sum. -/
theorem bandRegressionScore_eq_primeSum
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.bandRegressionScore q m =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandRegressionScore bandScore bandRegressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      q.1 (B.partition.band p) *
        valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  rw [hpj]

/-- The first-stage residual is exactly `S_g - sum_j q_j Omega_j`. -/
theorem postBandPrimeScore_eq_slow_sub_bandRegression
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      B.slowScore m - B.bandRegressionScore q m := by
  rw [B.bandRegressionScore_eq_primeSum q m]
  unfold postBandPrimeScore actualCompensatedCoefficient
    slowScore primeDeviation bandRegressionCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring







theorem inner_nuisanceCovarianceVector [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceVector xi F) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) F := by
  rw [PiLp.inner_apply]
  change (∑ c : NuisanceCoord B.HeadIndex,
      B.nuisanceCovarianceVector xi F c * z c) = _
  rw [show (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      fun m ↦ ∑ c : NuisanceCoord B.HeadIndex,
        z c * B.nuisanceStatistic m c by
    funext m
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rw [RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]
    ring]
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FiniteProbability.covariance_smul_left]
  simp only [B.nuisanceCovarianceVector_apply]
  ring





theorem nuisanceCoefficientOfScore_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceOperator xi
        (B.nuisanceCoefficientOfScore xi hgamma hgap F) =
      B.nuisanceCovarianceVector xi F := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

/-- Coercivity of the literal nuisance covariance block bounds the actual
regression coefficient by the norm of its literal covariance vector. -/
theorem nuisanceCoefficientOfScore_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap F‖ ≤
      ‖B.nuisanceCovarianceVector xi F‖ / gamma := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  have hcoer := hgap a
  rw [B.nuisanceCoefficientOfScore_solve xi hgamma hgap F] at hcoer
  have hinner : inner ℝ a (B.nuisanceCovarianceVector xi F) ≤
      ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ :=
    real_inner_le_norm _ _
  by_cases ha : ‖a‖ = 0
  · change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    rw [ha]
    exact div_nonneg (norm_nonneg _) (le_of_lt hgamma)
  · have hapos : 0 < ‖a‖ :=
      lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha)
    have hcancel : gamma * ‖a‖ ≤
        ‖B.nuisanceCovarianceVector xi F‖ := by
      have hmul : (gamma * ‖a‖) * ‖a‖ ≤
          ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
        calc
          (gamma * ‖a‖) * ‖a‖ = gamma * ‖a‖ ^ 2 := by ring
          _ ≤ inner ℝ a (B.nuisanceCovarianceVector xi F) := hcoer
          _ ≤ ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hapos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)





private theorem covariance_sub_right
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G H : Omega → ℝ) :
    mu.covariance F (fun omega ↦ G omega - H omega) =
      mu.covariance F G - mu.covariance F H := by
  have hfun : (fun omega ↦ G omega - H omega) =
      fun omega ↦ G omega + (-1 : ℝ) * H omega := by
    funext omega
    ring
  rw [hfun, mu.covariance_add_right, mu.covariance_smul_right]
  ring











/-- Exact marked-row identity for an arbitrary nuisance coefficient.  The
vector on the right is the literal covariance vector of the marked score,
so a Euclidean row estimate can be used without introducing a
coordinate-counting loss. -/
theorem covariance_marked_nuisanceScore_eq_inner [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance F
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      inner ℝ z (B.nuisanceCovarianceVector xi F) := by
  rw [(B.tiltedLaw xi).covariance_comm]
  exact (B.inner_nuisanceCovarianceVector xi F z).symm

/-- A coordinatewise nuisance-row estimate gives the Euclidean estimate used
in the second regression.  The only loss is the square root of the fixed
nuisance dimension.  Keeping this conversion explicit is useful in the
marked-row argument: the analytic input is naturally proved one physical or
head coordinate at a time, whereas the regression coefficient is controlled
in Euclidean norm. -/
theorem nuisanceCovarianceVector_norm_le_sqrt_card_mul [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c) F| ≤ K) :
    ‖B.nuisanceCovarianceVector xi F‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K := by
  have hsq : ‖B.nuisanceCovarianceVector xi F‖ ^ 2 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, B.nuisanceCovarianceVector_apply]
    calc
      (∑ c : NuisanceCoord B.HeadIndex,
          |(B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c) F| ^ 2) ≤
          ∑ _c : NuisanceCoord B.HeadIndex, K ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact pow_le_pow_left₀ (abs_nonneg _) (hcoord c) 2
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
        simp
  have hcard : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard
  have hrhs0 : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K :=
    mul_nonneg (Real.sqrt_nonneg _) hK
  have hrhsSq :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [mul_pow, hsqrt]
  rw [← hrhsSq] at hsq
  nlinarith [norm_nonneg (B.nuisanceCovarianceVector xi F)]

/-- A reciprocal marked row controls the covariance with the entire literal
post-band prime score by the actual compensated weighted `L¹` norm.  This is
the finite summation step used twice in Lemma 8.6: once for the nuisance
coefficient and once for a marked valuation row. -/
theorem abs_covariance_nuisance_postBandPrimeScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (c : NuisanceCoord B.HeadIndex) {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (B.postBandPrimeScore q)| ≤
        Cmarked * B.partition.compensatedL1 q := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.postBandPrimeScore q) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.actualCompensatedCoefficient q p *
            mu.covariance Z
              (fun m ↦ valuation p.1 (B.sampleData.value m)) := by
    unfold postBandPrimeScore
    rw [show (fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.actualCompensatedCoefficient q p *
          valuation p.1 (B.sampleData.value m)) =
      fun m ↦ ∑ p ∈ (Finset.univ :
          Finset (BandPrime B.sampleData.n B.sampleData.W)),
        B.actualCompensatedCoefficient q p *
          valuation p.1 (B.sampleData.value m) by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro p hp
    rw [mu.covariance_smul_right]
  change |mu.covariance Z (B.postBandPrimeScore q)| ≤ _
  rw [hsum]
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.actualCompensatedCoefficient q p *
          mu.covariance Z
            (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient q p *
            mu.covariance Z
              (fun m ↦ valuation p.1 (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.actualCompensatedCoefficient q p| *
          (Cmarked * (1 / (p.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmarked p) (abs_nonneg _)
    _ = Cmarked * B.partition.compensatedL1 q := by
      unfold ArithmeticBandGeometry.Partition.compensatedL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [B.partition_compensatedCoefficient_eq q p]
      ring

/-- Vector form of the reciprocal-row summation.  Thus the covariance vector
needed for the nuisance regression is a consequence of the same componentwise
marked estimates and of the already established coefficient `L¹` bound; it is
not a second independent analytic assumption. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.partition.compensatedL1 q) := by
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (by positivity) (abs_nonneg _)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.postBandPrimeScore q) (mul_nonneg hCmarked hL1nonneg)
  intro c
  exact B.abs_covariance_nuisance_postBandPrimeScore_le_of_marked
    xi q c (fun p ↦ hmarked c p)

/-- Scaled form used in the final `w²` assembly. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cmarked CL1 w : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1 q ≤ CL1 * w) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * CL1)) * w := by
  have hraw := B.nuisanceCovarianceVector_postBand_norm_le_of_marked
    xi q hCmarked hmarked
  calc
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.partition.compensatedL1 q) := hraw
    _ ≤ Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (CL1 * w)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hL1 hCmarked)
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * w := by ring

/-- The explicit nuisance contribution to a marked row is derived from the
two natural covariance-vector bounds and nuisance coercivity.  In
particular, later assembly need not assume the scalar marked nuisance row
itself. -/
theorem actualNuisanceCoefficient_markedRow_bound [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (F : B.sampleData.Sample → ℝ)
    {Cz Cmarked w rho : ℝ}
    (hCz : 0 ≤ Cz) (hw : 0 ≤ w)
    (hscore : ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore q)‖ ≤ Cz * w)
    (hmarked : ‖B.nuisanceCovarianceVector xi F‖ ≤
      Cmarked * rho) :
    |(B.tiltedLaw xi).covariance F
        (fun m ↦ inner ℝ
          (B.actualNuisanceCoefficient xi hgamma hgap q)
          (B.nuisanceStatistic m))| ≤
      ((Cz / gamma) * Cmarked) * w * rho := by
  have ha : ‖B.actualNuisanceCoefficient xi hgamma hgap q‖ ≤
      (Cz / gamma) * w := by
    unfold actualNuisanceCoefficient
    calc
      ‖B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.postBandPrimeScore q)‖ ≤
          ‖B.nuisanceCovarianceVector xi
            (B.postBandPrimeScore q)‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
      _ ≤ (Cz * w) / gamma :=
        div_le_div_of_nonneg_right hscore (le_of_lt hgamma)
      _ = (Cz / gamma) * w := by ring
  rw [B.covariance_marked_nuisanceScore_eq_inner]
  calc
    |inner ℝ (B.actualNuisanceCoefficient xi hgamma hgap q)
        (B.nuisanceCovarianceVector xi F)| ≤
        ‖B.actualNuisanceCoefficient xi hgamma hgap q‖ *
          ‖B.nuisanceCovarianceVector xi F‖ := abs_real_inner_le_norm _ _
    _ ≤ ((Cz / gamma) * w) * (Cmarked * rho) :=
      mul_le_mul ha hmarked (norm_nonneg _) (by
        exact mul_nonneg
          (div_nonneg hCz (le_of_lt hgamma)) hw)
    _ = ((Cz / gamma) * Cmarked) * w * rho := by ring

/-- Exact marked-row decomposition after nuisance regression. -/
theorem actualCompensatedScore_markedRow_decomposition [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.actualCompensatedScore xi hgamma hgap q) =
      (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.postBandPrimeScore q) -
        (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (fun m ↦ inner ℝ
            (B.actualNuisanceCoefficient xi hgamma hgap q)
            (B.nuisanceStatistic m)) := by
  exact covariance_sub_right _ _ _ _

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityMixtureTilt -/
section


/-!
# Exponential tilts of finite tagged mixtures

A global exponential tilt of a finite mixture is not obtained by retaining
the old cell weights.  The exact new weights contain the cell partition
functions.  This file proves that identity before any covariance is formed,
so common-profile estimates can safely be averaged across cells.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]









/-- Pointwise exact factorization of the globally tilted density into the
new cell weight and the componentwise tilted density. -/
theorem exponentialTilt_sigmaMixture_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (x : Sigma Omega) :
    ((sigmaMixture weight mu).exponentialTilt S).mass x =
      (sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c))).mass x := by
  rcases x with ⟨c, x⟩
  let Zc := (mu c).expPartition (sigmaCellScore S c)
  let Z := (sigmaMixture weight mu).expPartition S
  have hcellZ : Zc ≠ 0 :=
    ne_of_gt ((mu c).expPartition_pos (sigmaCellScore S c))
  have hglobalZ : Z ≠ 0 :=
    ne_of_gt ((sigmaMixture weight mu).expPartition_pos S)
  change weight.mass c * (mu c).mass x * Real.exp (S ⟨c, x⟩) / Z =
    (weight.mass c * Zc / Z) *
      ((mu c).mass x * Real.exp (S ⟨c, x⟩) / Zc)
  field_simp [hcellZ, hglobalZ]

private theorem finiteProbability_ext
    {Alpha : Type*} [Fintype Alpha]
    {mu nu : FiniteProbability Alpha} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
    cases nu with
    | mk massNu nonnegNu sumNu =>
      dsimp only at h
      subst massNu
      rfl

/-- Equality of the two finite probability laws, not merely equality of
their expectations. -/
theorem exponentialTilt_sigmaMixture
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).exponentialTilt S =
      sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c)) := by
  apply finiteProbability_ext
  funext x
  exact exponentialTilt_sigmaMixture_mass weight mu S x





end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeCellTiltDecomposition -/
section


/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



























/-- The actual bridge law, with the global cell partition functions handled
correctly, is a tagged mixture of the componentwise tilted guard-deleted
cell laws. -/
theorem tiltedLaw_eq_tiltedSigmaMixture [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦ (B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline]
  exact exponentialTilt_sigmaMixture _ _ _



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.DickmanFourMarkProductKernel -/
section


/-!
# The four-mark Dickman product kernel

The four-mark chamber in the proof of Lemma 7.5 uses the normalized
Dickman profile

`F x = rho (U - x) / rho U`

on the full simplex `x, z >= 0`, `x + z <= 4`.  The local product estimate
in `DickmanBasic` covers the unit square by differentiating the actual
method-of-steps solution near the origin.  This file extends that estimate
to the whole four-mark simplex using the globally proved one-Lipschitz
bound for `rho` on `[0,5]`.  In particular, no `C^{1,1}` hypothesis and no
tilt-box parameter occurs in the statement or proof.
-/

open Set

noncomputable section

namespace Erdos390.Full.DickmanFourMarkProductKernel

open DickmanBasic FriableAsymptotic















theorem boxIndependentFourMarkKernelConstant_pos :
    0 < boxIndependentFourMarkKernelConstant :=
  (Classical.choose_spec
    exists_boxIndependent_fourMark_productKernel_bound).1





end Erdos390.Full.DickmanFourMarkProductKernel

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section

























theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity















end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.PaperPrimePowerPairAggregation -/
section


/-!
# From actual prime-power pairs to a paper prime row

This file performs the finite aggregation that follows the pointwise
two-local estimates in Lemma 7.5.  Its inputs are covariances and moments of
the genuine divisor-indicator columns of an actual `BoundedValuationLaw`.
The preceding logarithmic-cutoff module makes every exponent range literal.

The factors `8`, `64`, and `quadraticHalfMass` are obtained from the proved
geometric series, rather than hidden in an `O`-constant.  A single universal
aggregation constant then feeds the already formalized paper-band row
contraction.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerPairAggregation

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff
open PrimeSums
open PaperPrimePowerRow

noncomputable section







lemma sixtyFour_le_pairAggregationConstant :
    (64 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  linarith [quadraticHalfMass_nonneg]



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)











end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerLemma75 -/
section


/-!
# Exact export of paper Lemma 7.5

This module joins the literal four-mark chamber, the arbitrary-power
fallback, the four prime-power orientations, and their finite row
aggregation.  The final constant is independent of the tilt box.  All box
dependence is confined to a single remainder tending to zero.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerLemma75

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open DickmanFourMarkProductKernel
open FullTiltPairChamber FullTiltPairHarmonicRate
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber PaperScaleMarkedCell LocalFugacityBounds
open PaperTwoLocalRestorationBound PaperValuationCutoff
open PaperPrimePowerChamberError PaperPrimePowerActualSplice
open PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerSumAbsAggregation
open ValuationCutoff PrimeSums PaperPrimePowerRow

noncomputable section





theorem paperPrimePowerConstant_pos {C_K : ℝ} (hCK : 0 < C_K) :
    0 < paperPrimePowerConstant C_K := by
  unfold paperPrimePowerConstant
  have hAgg : 0 < pairAggregationConstant :=
    lt_of_lt_of_le (by norm_num) sixtyFour_le_pairAggregationConstant
  have hMain : 0 < primePowerMainConstant C_K := by
    unfold primePowerMainConstant
    exact add_pos (mul_pos (by norm_num) hCK)
      (one_div_pos.mpr DickmanBasic.rho_U_pos)
  exact mul_pos (mul_pos hAgg hMain) (by positivity)











end

end Erdos390.Full.PaperPrimePowerLemma75

end

/- Source module: Erdos390.Full.FixedFiniteMixtureFullUniform -/
section


/-!
# Full uniform Lemma 7.5 for a fixed finite family of actual cells

This file specializes the marked-cell and full-tilt asymptotics on every
member of a fixed finite family, takes finite common majorants, and applies
the exact tagged-mixture theorem.  No desired covariance or tail estimate
is assumed by the final export.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureFullUniform

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate FullTiltPrimePowerFallback
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixtureLemma75 PaperValuationCutoff ValuationCutoff
open PrimeSums

noncomputable section









variable {Cell : Type*} [Fintype Cell]



theorem boxIndependentPrimePowerConstant_pos :
    0 < boxIndependentPrimePowerConstant :=
  paperPrimePowerConstant_pos boxIndependentFourMarkKernelConstant_pos



end

end Erdos390.Full.FixedFiniteMixtureFullUniform

end

/- Source module: Erdos390.Full.PaperPrimePowerRelativeQuadratic -/
section


/-!
# Relative prime-power quadratic transfer for Lemma 8.6

Lemma 7.5 supplies a genuine weighted row estimate for the difference
between full valuation covariance and squarefree covariance.  This file
proves, by finite summation, that the row estimate gives an error at the
relative `w^2` scale for the actual compensated coefficient vector.  The
proof does not replace `sum |Cov|` by `|sum Cov|`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRelativeQuadratic

open ArithmeticModel PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

noncomputable section

variable {Omega : Type*} [Fintype Omega] {M : ℕ}



















theorem fullMarked_sub_squarefree_eq
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) (p : ℕ) :
    fullMarkedRow law S c p - squarefreeMarkedRow law S c p =
      ∑ q ∈ S, c q * (law.covVV p q - law.covII p q) := by
  unfold fullMarkedRow squarefreeMarkedRow covVV covII
  rw [law.probability.covariance_sum_right,
    law.probability.covariance_sum_right,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_right,
    law.probability.covariance_smul_right]
  ring

/-- The genuine Lemma 7.5 row estimate gives the relative marked-prime
prime-power error, uniformly for every marked prime in the actual band. -/
theorem abs_fullMarked_sub_squarefree_le_of_row
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup w R : ℝ}
    (hCsup : 0 ≤ Csup) (hw : 0 ≤ w)
    (hcSup : ∀ q ∈ primeBand n W, |c q| ≤ Csup * w)
    (hrow : ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand n W) :
    |fullMarkedRow law (primeBand n W) c p -
        squarefreeMarkedRow law (primeBand n W) c p| ≤
      Csup * w * R * (1 / (p : ℝ)) := by
  have hpPos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hCw : 0 ≤ Csup * w := mul_nonneg hCsup hw
  rw [fullMarked_sub_squarefree_eq]
  calc
    |∑ q ∈ primeBand n W,
        c q * (law.covVV p q - law.covII p q)| ≤
      ∑ q ∈ primeBand n W,
        |c q * (law.covVV p q - law.covII p q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ primeBand n W,
        |c q| * |law.covVV p q - law.covII p q| := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [abs_mul]
    _ ≤ ∑ q ∈ primeBand n W,
        (Csup * w) * |law.covVV p q - law.covII p q| := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hcSup q hq) (abs_nonneg _)
    _ = (Csup * w) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| := by
      rw [Finset.mul_sum]
    _ ≤ (Csup * w) * (R / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hCw
      exact (le_div_iff₀ hpPos).2 (by
        simpa only [mul_comm] using hrow p hp)
    _ = Csup * w * R * (1 / (p : ℝ)) := by
      field_simp [ne_of_gt hpPos]



end

end Erdos390.Full.PaperPrimePowerRelativeQuadratic

end

/- Source module: Erdos390.Full.PaperActualPrimePowerRelative -/
section


/-!
# Actual bridge specialization of the relative prime-power transfer

This file constructs the bounded valuation law directly from the genuine
guard-deleted tilted bridge sample.  It then applies the weighted row theorem
to the literal post-regression coefficients from Lemma 8.6.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- The subtype and natural-prime `L¹` sums are exactly the same finite sum. -/
theorem compensatedNatL1_eq_partition
    (q : B.RawBandGauge) :
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ))) =
      B.partition.compensatedL1 q := by
  unfold ArithmeticBandGeometry.Partition.compensatedL1
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ)))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]
  rw [B.partition_compensatedCoefficient_eq q p]
  ring

/-- The primewise post-band score is the full-valuation score of the actual
bounded valuation law. -/
theorem postBandPrimeScore_eq_actualValuationSum [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q p *
          (B.actualValuationLaw xi).V p m := by
  unfold postBandPrimeScore actualValuationLaw
    PrimePowerCovariance.BoundedValuationLaw.V
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ B.actualCompensatedNatCoefficient q p *
      valuation p (B.sampleData.value m))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]





/-- Exact marked-row identification for the actual full and squarefree
post-band scores. -/
theorem actualMarkedRows_eq_covariances [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    fullMarkedRow (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) p =
      (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.postBandPrimeScore q) ∧
    squarefreeMarkedRow (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) p =
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) := by
  constructor
  · unfold fullMarkedRow actualValuationLaw
      PrimePowerCovariance.BoundedValuationLaw.V
    congr 1
    funext m
    exact (B.postBandPrimeScore_eq_actualValuationSum xi q m).symm
  · rfl





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualTwoStageRegression -/
section


/-!
# The literal two-stage band/nuisance solve of Lemma 8.6

This file defines the actual Schur-projected band operator on the exact raw
arithmetic gauge.  The first regression vector is obtained by inverting this
literal operator on the literal Schur-projected raw slow-score column.  The
second regression is then the actual nuisance inverse already constructed in
`PaperActualCompensatedRegression`.

No covariance matrix, inverse, or regression conclusion is stored in bridge
data.  The equivalence argument of the first-stage constructor is intended to
be supplied by the actual projected inverse conclusion of Lemma 8.4.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open CompressedArithmeticOperator
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







































theorem bandRegressionScore_sub
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q - r) =
      fun m ↦ B.bandRegressionScore q m - B.bandRegressionScore r m := by
  have hneg : -r = (-1 : ℝ) • r := (neg_one_smul ℝ r).symm
  rw [sub_eq_add_neg, B.bandRegressionScore_add, hneg,
    B.bandRegressionScore_smul]
  funext m
  ring







































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperVectorFieldSchur -/
section


/-!
# Exact Schur decomposition of the paper vector field

The nonlinear ODE uses the literal vector field

`(D M(xi))^{-1} target`.

This file proves, for the actual finite covariance operator and the actual
paper coordinates, that its main and nuisance coordinate blocks are obtained
by the same exact Schur solve used in Lemmas 8.4 and 8.6.  No inverse estimate,
covariance gap, or marked-row estimate is packaged as data here.  The only
positivity hypotheses are the pointwise gaps needed to make the two displayed
finite linear maps invertible.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













/-- The two coordinate projections recombine to the original parameter. -/
theorem combine_mainPart_nuisancePart (x : B.ParamSpace) :
    B.combine (B.mainPart x) (B.nuisancePart x) = x := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c <;> simp [combine]

/-- The main coordinate projection is the adjoint of the main inclusion. -/
theorem mainEmbedding_adjoint_apply (x : B.ParamSpace) :
    B.mainEmbeddingCLM.adjoint x = B.mainPart x := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hx := B.combine_mainPart_nuisancePart x
  change inner ℝ (B.mainEmbed u) x = inner ℝ u (B.mainPart x)
  calc
    inner ℝ (B.mainEmbed u) x =
        inner ℝ (B.mainEmbed u)
          (B.combine (B.mainPart x) (B.nuisancePart x)) := by rw [hx]
    _ = inner ℝ u (B.mainPart x) :=
      B.inner_mainEmbed_combine u (B.mainPart x) (B.nuisancePart x)

/-- The nuisance coordinate projection is the adjoint of the nuisance
inclusion. -/
theorem nuisanceEmbedding_adjoint_apply (x : B.ParamSpace) :
    B.nuisanceEmbeddingCLM.adjoint x = B.nuisancePart x := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hx := B.combine_mainPart_nuisancePart x
  change inner ℝ (B.nuisanceEmbed z) x = inner ℝ z (B.nuisancePart x)
  calc
    inner ℝ (B.nuisanceEmbed z) x =
        inner ℝ (B.nuisanceEmbed z)
          (B.combine (B.mainPart x) (B.nuisancePart x)) := by rw [hx]
    _ = inner ℝ z (B.nuisancePart x) :=
      B.inner_nuisanceEmbed_combine z (B.nuisancePart x) (B.mainPart x)

/-- The normalized covariance operator sends the actual inverse-Jacobian
vector field to the normalized paper target. -/
theorem covarianceOperator_vectorField [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi) :
    B.covarianceOperator xi
        (B.vectorFamily.vectorField (B.targetVector Delta) xi) =
      B.normalizedTarget Delta := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply,
    B.vectorFamily.jacobian_vectorField (B.targetVector Delta) hgamma hgap]
  rfl

/-- Exact nuisance block of the actual covariance equation. -/
theorem nuisancePart_covarianceOperator_combine [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.nuisancePart (B.covarianceOperator xi (B.combine u z)) =
      B.crossCovarianceOperator xi u +
        B.nuisanceCovarianceOperator xi z := by
  rw [← B.nuisanceEmbedding_adjoint_apply]
  change B.nuisanceEmbeddingCLM.adjoint
      (B.covarianceOperator xi (B.mainEmbed u + B.nuisanceEmbed z)) =
    B.nuisanceEmbeddingCLM.adjoint
        (B.covarianceOperator xi (B.mainEmbed u)) +
      B.nuisanceEmbeddingCLM.adjoint
        (B.covarianceOperator xi (B.nuisanceEmbed z))
  simp only [map_add]

/-- Exact main block after inserting the actual nuisance regression. -/
theorem mainPart_covarianceOperator_schurResidual [Nonempty Head]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.mainPart (B.covarianceOperator xi
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) =
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u := by
  rw [← B.mainEmbedding_adjoint_apply]
  simp only [exactSchurCovarianceOperator,
    ContinuousLinearMap.comp_apply, B.exactSchurEmbeddingCLM_apply]



set_option maxHeartbeats 1000000 in
/-- The actual inverse-Jacobian vector field is exactly a Schur residual,
and its main coordinate solves the literal Schur equation. -/
theorem vectorField_eq_schurResidual_and_mainEquation [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
    let u := B.mainPart v
    v = B.schurResidual
        (B.exactNuisanceRegression xi hgammaNuisance hGamma) u ∧
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
        B.mainPart (B.normalizedTarget Delta) := by
  dsimp only
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let z := B.nuisancePart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hvDecomp : B.combine u z = v := by
    exact B.combine_mainPart_nuisancePart v
  have hsolve : B.covarianceOperator xi v = B.normalizedTarget Delta :=
    B.covarianceOperator_vectorField xi Delta hgammaFull hFull
  have hnuisance :
      B.crossCovarianceOperator xi u +
        B.nuisanceCovarianceOperator xi z = 0 := by
    have h := congrArg B.nuisancePart hsolve
    rw [← hvDecomp, B.nuisancePart_covarianceOperator_combine,
      B.nuisancePart_normalizedTarget] at h
    exact h
  have hz : z = -R u := by
    apply B.nuisanceCovarianceOperator_injective xi hgammaNuisance hGamma
    have hRu : B.nuisanceCovarianceOperator xi (R u) =
        B.crossCovarianceOperator xi u := by
      exact B.exactNuisanceRegression_solve xi hgammaNuisance hGamma u
    rw [map_neg, hRu]
    rw [eq_neg_iff_add_eq_zero]
    calc
      B.nuisanceCovarianceOperator xi z +
          B.crossCovarianceOperator xi u =
        B.crossCovarianceOperator xi u +
          B.nuisanceCovarianceOperator xi z := add_comm _ _
      _ = 0 := hnuisance
  have hvSchur : v = B.schurResidual R u := by
    rw [← hvDecomp, hz]
    rfl
  refine ⟨?_, ?_⟩
  · simpa only [v, u, R] using hvSchur
  · have hmain := congrArg B.mainPart hsolve
    rw [hvSchur,
      B.mainPart_covarianceOperator_schurResidual] at hmain
    simpa only [u, R] using hmain





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMainRawGaugeCoordinates -/
section


/-!
# Exact identification of the main coordinates with the paper raw gauge

The ODE parameter space stores one coordinate for each concrete gauge-basis
vector and stores `w * lambda` in the slow coordinate.  Lemma 8.6 instead
writes the band coefficient as a vector in the arithmetic hyperplane
`sum_j H_j alpha_j q_j = 0`.  This file identifies these two descriptions
exactly, including the moving low coordinate.  No estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























/-- Exact effective prime coefficient of a Schur residual. -/
theorem schurResidual_effectivePrimeCoefficient
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.schurResidual R u) p =
      (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p := by
  rw [B.schurResidual_eq_sub]
  have hadd := B.effectivePrimeCoefficient_add
    (B.mainEmbed u) (-B.nuisanceEmbed (R u)) p
  have hneg := B.effectivePrimeCoefficient_smul (-1)
    (B.nuisanceEmbed (R u)) p
  rw [sub_eq_add_neg, hadd]
  change B.effectivePrimeCoefficient (B.mainEmbed u) p +
      B.effectivePrimeCoefficient (-B.nuisanceEmbed (R u)) p = _
  rw [show -B.nuisanceEmbed (R u) =
      (-1 : ℝ) • B.nuisanceEmbed (R u) by simp,
    hneg, B.nuisanceEmbed_effectivePrimeCoefficient]
  simp





/-- Exact score represented by a main parameter in intrinsic raw-gauge and
stored-slow coordinates.  The factor `1 / w` is visible because the actual
`MainSpace` stores `w * lambda`. -/
theorem vectorScore_mainEmbed_eq_rawGauge_add_slow [Nonempty Head]
    (u : B.MainSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.mainEmbed u) = 0 := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  rw [hnuisance, inner_zero_left, add_zero]
  simp_rw [B.mainEmbed_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ ↦ x + y) rfl
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact score of a Schur residual.  This is the literal finite score on
which the band and marked covariance rows act. -/
theorem vectorScore_schurResidual_eq_rawGauge_slow_nuisance
    [Nonempty Head]
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.schurResidual R u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m -
          inner ℝ (R u) (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance,
    B.nuisanceParameter_schurResidual]
  simp_rw [B.schurResidual_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [inner_neg_left]
  have hslow :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        u MainCoord.slow / B.w * B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m)) =
        (u MainCoord.slow / B.w) *
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation p *
              ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hslow]
  ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactSchurRawSlow -/
section


/-!
# Exact raw-gauge/slow form of the finite Schur regression

This file identifies the nuisance regression occurring in the actual Schur
operator with the regression of the literal raw-gauge/slow score.  It is an
exact finite-dimensional identity, and is the first attachment needed to
turn the two-stage estimates of Lemma 8.6 into bounds for the Proposition
8.7 vector field.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The exponential-family score of a pure nuisance parameter is exactly
the Euclidean pairing with the literal physical/head statistic. -/
theorem vectorScore_nuisanceEmbed_eq_nuisanceStatistic [Nonempty Head]
    (z : B.NuisanceSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.nuisanceEmbed z) =
      inner ℝ z (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.nuisanceEmbed z) = z := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  simp_rw [B.nuisanceEmbed_effectivePrimeCoefficient]
  rw [hnuisance]
  simp

/-- The main-to-nuisance covariance block is the covariance vector of the
literal main score. -/
theorem crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) :
    B.crossCovarianceOperator xi u =
      B.nuisanceCovarianceVector xi
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply ext_inner_left ℝ
  intro z
  have hcross :
      inner ℝ z (B.crossCovarianceOperator xi u) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.mainEmbed u)) := by
    simpa only [crossCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right
        B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u)))
  rw [hcross, B.inner_covarianceOperator,
    B.inner_nuisanceCovarianceVector]
  congr 1
  funext m
  calc
    inner ℝ (B.nuisanceEmbed z) (B.statistic m) =
        inner ℝ (B.statistic m) (B.nuisanceEmbed z) :=
      real_inner_comm _ _
    _ = inner ℝ z (B.nuisanceStatistic m) := by
      simpa only [VectorExponentialFamily.scalarFamily,
        innerSL_apply_apply] using
          B.vectorScore_nuisanceEmbed_eq_nuisanceStatistic z m
  funext m
  simpa only [VectorExponentialFamily.scalarFamily,
    innerSL_apply_apply] using
      (real_inner_comm (B.mainEmbed u) (B.statistic m)).symm

/-- The nuisance component of the exact Schur residual is the actual finite
regression coefficient of the literal main score. -/
theorem exactNuisanceRegression_eq_nuisanceCoefficient_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.exactNuisanceRegression_solve,
    B.nuisanceCoefficientOfScore_solve]
  exact B.crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore xi u

/-- Consequently the score of the exact Schur residual is literally the
nuisance residual of the raw main score. -/
theorem vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      B.nuisanceResidualScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  funext m
  rw [B.vectorScore_schurResidual_eq_rawGauge_slow_nuisance]
  unfold nuisanceResidualScore
  rw [← B.exactNuisanceRegression_eq_nuisanceCoefficient_mainScore]
  change _ =
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) -
      inner ℝ (B.exactNuisanceRegression xi hgamma hgap u)
        (B.nuisanceStatistic m)
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]

/-- Exact fast/slow score decomposition used by the full block inverse.  If
the raw gauge coordinate has the algebraic form

`q_fast - lambda * q_reg`

and the stored slow coordinate is `w * lambda`, then the Schur-residual
score is the nuisance-projected fast score plus `lambda` times the literal
two-stage compensated score.  This is the finite identity behind the marked
row integration in Proposition 8.7. -/
theorem vectorScore_exactSchurResidual_fast_add_compensated
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) (qFast qReg : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda • qReg)
    (hslow : u MainCoord.slow = B.w * lambda) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      fun m ↦
        B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast) m +
          lambda * B.actualCompensatedScore xi hgamma hgap qReg m := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  have hinput :
      (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) =
        fun m ↦ B.bandRegressionScore qFast m +
          lambda * B.postBandPrimeScore qReg m := by
    funext m
    rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow, hq,
      B.bandRegressionScore_sub,
      B.bandRegressionScore_smul, hslow,
      mul_div_cancel_left₀ lambda (ne_of_gt B.w_pos),
      B.postBandPrimeScore_eq_slow_sub_bandRegression]
    ring
  rw [hinput, B.nuisanceResidualScore_add,
    B.nuisanceResidualScore_smul]
  rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperVectorFieldEffectiveBound -/
section


/-!
# Effective-norm bound for the literal paper vector field

The ODE continuation argument uses the effective max norm, not the ambient
Euclidean norm.  This file proves the exact finite identity which converts
the Schur solution into its three paper components:

* the prime-by-prime effective fugacity;
* the nuisance regression coefficient;
* the stored slow coordinate `w * lambda`.

It then shows that uniform bounds for those three components of every
solution of the *actual* Schur equation imply the required effective
velocity bound.  Thus Proposition 8.7 can consume the literal quantitative
outputs of Lemmas 8.4--8.6 without assuming a norm bound for the already
assembled vector field.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- Primewise marked-row transfer for the literal vector field.  The fast
Schur residual and the compensated slow score are kept separate, exactly as
in the proof of Proposition 8.7.  A `O(w rho)` compensated row multiplied by
the proved `O(1/w)` slow velocity contributes only `O(rho)`; no endpoint
estimate is assumed here. -/
theorem vectorField_markedRow_le_of_fast_compensated
    [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (p : ℕ) (qFast qReg : B.RawBandGauge) (lambda : ℝ)
    {Cfast Ccomp Cslow rho : ℝ}
    (hCslow : 0 ≤ Cslow)
    (hq : B.rawGaugeOfMain
        (B.mainPart (B.vectorFamily.vectorField
          (B.targetVector Delta) xi)) = qFast - lambda • qReg)
    (hslowCoord :
      B.mainPart (B.vectorFamily.vectorField
          (B.targetVector Delta) xi) MainCoord.slow = B.w * lambda)
    (hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore qFast))| ≤ Cfast * rho)
    (hcompensated :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualCompensatedScore xi hgammaNuisance hGamma qReg)| ≤
          (Ccomp * rho) * B.w)
    (hlambda : |lambda| ≤ Cslow / B.w) :
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (Cfast + Cslow * Ccomp) * rho := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hv :=
    (B.vectorField_eq_schurResidual_and_mainEquation xi Delta
      hgammaFull hFull hgammaNuisance hGamma).1
  have hscore :=
    B.vectorScore_exactSchurResidual_fast_add_compensated
      xi hgammaNuisance hGamma u qFast qReg lambda
      (by simpa only [u, v] using hq)
      (by simpa only [u, v] using hslowCoord)
  change |(B.tiltedLaw xi).covariance (B.markedValuation p)
    (fun m ↦ B.vectorFamily.scalarFamily.score m v)| ≤ _
  have hv' : v = B.schurResidual R u := by
    simpa only [v, u, R] using hv
  rw [hv']
  change |(B.tiltedLaw xi).covariance (B.markedValuation p)
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual R u))| ≤ _
  have hscore' :
      (fun m ↦ B.vectorFamily.scalarFamily.score m
        (B.schurResidual R u)) =
      fun m ↦
        B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore qFast) m +
          lambda *
            B.actualCompensatedScore xi hgammaNuisance hGamma qReg m := by
    simpa only [R] using hscore
  rw [hscore', FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_smul_right]
  exact Erdos390.effective_prime_velocity_bound
    ((B.tiltedLaw xi).covariance (B.markedValuation p)
      (B.nuisanceResidualScore xi hgammaNuisance hGamma
        (B.bandRegressionScore qFast)))
    ((B.tiltedLaw xi).covariance (B.markedValuation p)
      (B.actualCompensatedScore xi hgammaNuisance hGamma qReg))
    lambda B.w (Cfast * rho) (Ccomp * rho) Cslow
    B.w_pos hCslow hfast hcompensated hlambda |>.trans_eq (by ring)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageTargetSolve -/
section


/-!
# Exact two-stage solution of the finite Schur target equation

This file performs the algebraic block solve which is used, but usually
left implicit, in Proposition 8.7.  The right side is the literal normalized
paper target.  Its fast band component and compensated slow component are
defined below from the actual finite arithmetic data.  No asymptotic
estimate, continuum operator, or covariance lower bound is asserted here.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























theorem rawGauge_eq_fastGauge_sub_regression
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) :
    B.rawGaugeOfMain u =
      B.fastGaugeOfMain xi hgamma hgap e u -
        (u MainCoord.slow / B.w) •
          B.actualBandRegression xi hgamma hgap e := by
  unfold fastGaugeOfMain
  abel

theorem slow_eq_w_mul_slow_div (u : B.MainSpace) :
    u MainCoord.slow = B.w * (u MainCoord.slow / B.w) := by
  field_simp [ne_of_gt B.w_pos]



/-- Consequently the fast coordinate is literally the inverse image of the
projected normalized target row. -/
theorem fastGauge_eq_inverse_projectedTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.fastGaugeOfMain xi hgamma hgap e u =
      e.symm (B.projectedNormalizedTargetBand Delta) := by
  apply e.injective
  rw [e.apply_symm_apply, he]
  exact B.actualBandSchur_fastGauge_eq_projectedTarget
    xi hgamma hgap e he Delta u hu





















/-- Division form of the exact slow solve. -/
theorem slow_div_eq_compensatedTarget_div_variance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    (hvariance : B.actualTwoStageCompensatedVariance
      xi hgamma hgap e ≠ 0) :
    u MainCoord.slow / B.w =
      B.compensatedNormalizedTarget xi hgamma hgap e Delta /
        B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  apply (eq_div_iff hvariance).2
  exact B.slow_div_mul_actualTwoStageCompensatedVariance
    xi hgamma hgap e he Delta u hu



/-- A lower bound for the literal compensated variance and an upper bound
for its literal target give the exact slow-velocity estimate. -/
theorem abs_slow_div_le_of_variance_target_bounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta))
    {Vlower Tbound : ℝ} (hVlower : 0 < Vlower)
    (hvariance : Vlower ≤ B.actualTwoStageCompensatedVariance
      xi hgamma hgap e)
    (hTbound : 0 ≤ Tbound)
    (htarget : |B.compensatedNormalizedTarget
      xi hgamma hgap e Delta| ≤ Tbound) :
    |u MainCoord.slow / B.w| ≤ Tbound / Vlower := by
  have hVpos : 0 < B.actualTwoStageCompensatedVariance
      xi hgamma hgap e := hVlower.trans_le hvariance
  have hformula := B.slow_div_eq_compensatedTarget_div_variance
    xi hgamma hgap e he Delta u hu (ne_of_gt hVpos)
  rw [hformula, abs_div, abs_of_pos hVpos]
  calc
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| /
        B.actualTwoStageCompensatedVariance xi hgamma hgap e ≤
      Tbound / B.actualTwoStageCompensatedVariance
        xi hgamma hgap e :=
      div_le_div_of_nonneg_right htarget hVpos.le
    _ ≤ Tbound / Vlower :=
      div_le_div_of_nonneg_left hTbound hVlower hvariance





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.SquarefreeCovarianceReference -/
section


/-!
# Signed squarefree covariance transfer to the Dickman kernel

The prime-power ledger only needs an absolute upper bound.  Lemma 8.4 needs
the stronger *signed* comparison between the genuine divisor-indicator
covariance and the arithmetic Poisson--Dickman matrix.  This file derives
that comparison from the same common one- and two-divisor profiles, before
any band averaging.  In particular, the between-cell covariance of the
tagged mixture is retained exactly.
-/

namespace Erdos390.Full.SquarefreeCovarianceReference

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber
open PaperScaleMarkedCell PaperPrimePowerChamberError
open FullTiltPrimePowerCovariance
open FixedFiniteMixturePrimePower
open DickmanFourMarkProductKernel ConditionedPoissonLimit

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}













/-- The signed one- and two-divisor comparisons assembled into the single
entrywise estimate consumed by the sharp band-row theorem. -/
theorem sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    ∀ p q : ArithmeticBandGeometry.BandPrime n W,
      |mix.covII p.1 q.1 - squarefreeReferenceEntry n p.1 q.1| ≤
        (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            (2 * E) / (p.1 : ℝ) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 +
                CKernel) / (p.1 : ℝ) ^ 2
          else 0) := by
  dsimp only
  let mix := sigmaMixture weight law
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    have hdiag := abs_sigmaMixture_covII_diagonal_sub_reference_le
      hE weight law hn p.2 (fun c ↦ hsingle c p.1 p.2)
      (hKernel p.1 p.2)
    have hcovNonneg : 0 ≤ pairCovarianceScale E :=
      pairCovarianceScale_nonneg hE
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hextra : 0 ≤
        (4 * pairCovarianceScale E) / ((p.1 : ℝ) * (p.1 : ℝ)) :=
      div_nonneg (mul_nonneg (by norm_num) hcovNonneg)
        (mul_nonneg hpPos.le hpPos.le)
    exact hdiag.trans (by
      have htwo : 2 * E / (p.1 : ℝ) = (2 * E) / (p.1 : ℝ) := rfl
      rw [htwo]
      linarith)
  · rw [if_neg hpq]
    have hqErase : q.1 ∈ (primeBand n W).erase p.1 :=
      Finset.mem_erase.mpr ⟨fun h ↦ hpq (Subtype.ext h.symm), q.2⟩
    have hoff :=
      abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
      hE weight law hn p.2 hqErase
      (fun c ↦ hpair c p.1 p.2 q.1 hqErase)
      (fun c ↦ hsingle c p.1 p.2)
      (fun c ↦ hsingle c q.1 q.2)
    have href : squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 := by
      rw [squarefreeReferenceEntry, if_neg (by
        intro h
        exact hpq (Subtype.ext h))]
    rw [href]
    have hrewrite :
        pairCovarianceScale E * pairWeight p.1 q.1 1 1 =
          (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) := by
      unfold pairWeight
      norm_num
      ring
    simpa only [mix, hrewrite, add_zero] using hoff



end

end Erdos390.Full.SquarefreeCovarianceReference

end

/- Source module: Erdos390.Full.PaperActualSquarefreeReference -/
section


/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





















private theorem boundedValuationLaw_ext
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    {law₁ law₂ : BoundedValuationLaw Omega M}
    (hprob : law₁.probability = law₂.probability)
    (hvalue : law₁.value = law₂.value) : law₁ = law₂ := by
  cases law₁
  cases law₂
  dsimp only at hprob hvalue
  subst_vars
  rfl

/-- The component mixture just constructed is literally the paper's global
tilted bounded valuation law.  In particular no between-cell covariance is
discarded. -/
theorem sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
    sigmaMixture weight (B.actualComponentValuationLaw xi) =
      B.actualValuationLaw xi := by
  dsimp only
  apply boundedValuationLaw_ext
  · exact congrArg id (B.tiltedLaw_eq_tiltedSigmaMixture xi).symm
  · rfl













/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/



























/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageOrdinaryFast -/
section


/-!
# Ordinary-fast / sharp-slow form of the exact two-stage solve

The fast target in Proposition 8.7 is bounded in the ordinary raw-band
supremum norm: its unprojected coordinates are
`(L / q) * Delta_j / H_j = O(1)`.  They are not, in general, bounded after
division by the moving centre `alpha_j`; in particular `alpha_0 -> 0`.

The slow regression is different.  Lemma 8.5 supplies a sharp inverse for
that right-hand side and hence a regression vector of size `O(w alpha_j)`.
This file records the exact finite algebra with those two norms kept
separate.  It is the norm-correct form of the block calculation in the
proof of Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Summing the literal band masses recovers the full reciprocal mass of
the actual prime band.  This exposes the sole `log L` loss in the ordinary
fast nuisance row. -/
theorem sum_harmonicMass_eq_bandReciprocalSum :
    (∑ j : Band, B.harmonicMass j) =
      PrimeSums.bandReciprocalSum B.sampleData.n B.sampleData.W := by
  calc
    (∑ j : Band, B.harmonicMass j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          (1 / (p.1 : ℝ)) := by
      unfold harmonicMass ArithmeticBandGeometry.Partition.mass
        Erdos390.Lemma84.WeightedBandData.mass
      rw [← Finset.sum_fiberwise Finset.univ B.partition.band
        (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
          (1 / (p.1 : ℝ)))]
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    _ = PrimeSums.bandReciprocalSum
        B.sampleData.n B.sampleData.W := by
      unfold PrimeSums.bandReciprocalSum
      have hattach := Finset.sum_attach
        (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
        (fun p ↦ 1 / (p : ℝ))
      simpa only [Finset.univ_eq_attach] using hattach































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperGuardPowerCorrectionMixture -/
section


/-!
# Guard deletion for the global prime-power correction row

The useful object in Lemma 7.5 is not the full valuation covariance by
itself, but its difference from the squarefree covariance.  This file applies
the family-summed tagged-mixture perturbation theorem separately to the `VV`
and `II` rows and then subtracts them.  The estimate is global: arbitrary
common component weights and every between-cell covariance term are included.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel ArithmeticBandGeometry FiniteProbability PaperBridgeFit

noncomputable section





theorem guardPowerCorrectionRowError_nonneg {K d : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ d) :
    0 ≤ guardPowerCorrectionRowError K d := by
  unfold guardPowerCorrectionRowError
  positivity

variable {Head : Type*} [Fintype Head]



end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow -/
section


/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







theorem physicalPowerCorrectionRowError_nonneg
    {epsilon G : ℝ} {n W : ℕ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) :
    0 ≤ physicalPowerCorrectionRowError epsilon G n W := by
  unfold physicalPowerCorrectionRowError bandReciprocalSum
  have hQ : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity















































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection -/
section


/-!
# The canonical guard contribution to the prime-power correction row

The prime-power reference law in Lemma 8.4 lives on the unguarded raw
structured cells, whereas the medium-only bridge law lives on the literal
guard-deleted cells.  This file compares the two tagged mixtures without
changing their (post-tilt) component weights.  The comparison includes all
between-component covariance terms.

No arbitrary `BridgeData` is declared canonical.  The finite comparison is
stated under the exact equality between its `sampleData` field and the
canonical constructor from `PaperGuardedStructuredSample`; all dependent
sample-space identifications are then obtained from
`canonicalSampleData_cellFinset`.
-/

open scoped BigOperators
open Filter Topology

set_option maxRecDepth 5000

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw StructuredCells
open PaperGuardCensus GuardedUniformCell
open ValuationScoreDomination

namespace BridgeData



variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















omit [DecidableEq Head] in theorem canonicalGuardPerturbationConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Kscore : ℝ) :
    0 ≤ canonicalGuardPerturbationConstant P I Kscore := by
  unfold canonicalGuardPerturbationConstant
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)).le





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalPhysicalPowerCorrectionEventually -/
section


/-!
# Eventual canonical specialization of the residual physical power row

This file discharges the density, score-envelope, small-tilt, and divisor
fallback inputs of the residual-physical comparison.  All constants are
chosen from the fixed physical cells, cutoff, and preselected coefficient
box.  The resulting row error is also proved to survive division by the
moving-low centre, via its explicit `error * log L -> 0` rate.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]







omit [Fintype Head] [DecidableEq Head] in
theorem canonicalPhysicalCellDensity_pos
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (c : Cell Head) :
    0 < canonicalPhysicalCellDensity P I c := by
  unfold canonicalPhysicalCellDensity
  exact div_pos
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2))
    (mul_pos (by norm_num)
      ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))

omit [DecidableEq Head] in
theorem canonicalPhysicalPowerCorrectionConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (W : ℕ) (Acoef : ℝ) :
    0 ≤ canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef := by
  unfold canonicalPhysicalPowerCorrectionConstant
  exact Finset.sum_nonneg fun c _ ↦
    div_nonneg (Real.exp_pos _).le
      (canonicalPhysicalCellDensity_pos P I c).le





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualPrimePowerRowTransfer -/
section


/-!
# Actual prime-power transfer from a reference row

The canonical raw Lemma 7.5 certificate is proved for an unguarded reference
law, whereas Lemma 8.6 uses the genuinely guarded and physically tilted law.
This file records the exact finite triangle needed to pass between them.

Only the weighted `VV-II` row is used.  This is deliberate: the compensated
slow coefficient contains the within-band deviation and therefore is not a
lift of a band vector.  A sharp band-operator estimate alone does not control
that coefficient.  The row below does, without postulating a full
`PrimePowerTransferBounds` package for the actual law.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- Marked-prime counterpart of
`actual_primePower_relative_variance_bound_of_row`. -/
theorem actual_primePower_relative_markedRow_bound_of_row
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      (1 + C) * w * R * (1 / (p : ℝ)) := by
  have hcSup :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).1
  have hnatSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ (1 + C) * w := by
    intro r hr
    rw [B.actualCompensatedNatCoefficient_of_mem q hr]
    rw [← B.partition_compensatedCoefficient_eq q ⟨r, hr⟩]
    exact hcSup ⟨r, hr⟩
  have hrowNat : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      (r : ℝ) * ∑ s ∈ primeBand B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV r s -
          (B.actualValuationLaw xi).covII r s| ≤ R := by
    intro r hr
    have hrowSubtype := hrow ⟨r, hr⟩
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun s ↦ |(B.actualValuationLaw xi).covVV r s -
        (B.actualValuationLaw xi).covII r s|)
    change (r : ℝ) *
      (∑ s ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |(B.actualValuationLaw xi).covVV r s.1 -
          (B.actualValuationLaw xi).covII r s.1|) ≤ R at hrowSubtype
    rw [hattach] at hrowSubtype
    simpa only using hrowSubtype
  have hmarked := abs_fullMarked_sub_squarefree_le_of_row
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    (show 0 ≤ 1 + C by linarith) hw hnatSup hrowNat hp
  obtain ⟨hfull, hsf⟩ := B.actualMarkedRows_eq_covariances xi q p
  rw [hfull, hsf] at hmarked
  simpa only [mul_assoc] using hmarked

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullProjectedInverseEventually -/
section


/-!
# Eventual inverse for the literal actual full projected operator

This file performs the two stable perturbations in the order used in
Section 8.4.  First the canonical arithmetic reference is perturbed to the
actual squarefree operator; then the proved full-versus-squarefree sharp row
is inserted.  The two perturbation radii and every inverse constant are
chosen before the ambient integer.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



















omit [DecidableEq Head] in theorem canonicalCombinedPowerCorrection_nonneg
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals)
    {Cmax Acoef Aphys : ℝ} {Cprom Cbank W n : ℕ}
    (hCmax : 1 ≤ Cmax)
    (hAphys : 0 ≤ Aphys) (hW : 1 < W) (hn : 1 < n) :
    0 ≤ canonicalCombinedPowerCorrection
      P I Cmax Cprom Cbank W Acoef Aphys n := by
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hlogCmax : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hepsilon : 0 ≤
      canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n := by
    unfold canonicalPhysicalPowerCorrectionEpsilon
    exact div_nonneg (mul_nonneg hAphys hlogCmax) hLpos.le
  have hG : 0 ≤
      canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef :=
    canonicalPhysicalPowerCorrectionConstant_nonneg P I Cmax W Acoef
  have hphysical : 0 ≤
      physicalPowerCorrectionRowError
        (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
        (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W :=
    physicalPowerCorrectionRowError_nonneg hepsilon hG
  have hCenv : 0 ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax W :=
    PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hD : 0 ≤ canonicalGuardPerturbationConstant P I
      (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W) :=
    canonicalGuardPerturbationConstant_nonneg P I _
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hcensus : 0 ≤
      PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
    unfold PaperGuardCensus.censusRatioMajorant
    have hcoef : 0 ≤ (Cprom : ℝ) +
        3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn0).le) (by positivity)
  have hguard : 0 ≤ guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n := by
    unfold guardPowerCorrectionWeightedMajorant
    exact mul_nonneg (Nat.cast_nonneg _)
      (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
        (mul_nonneg hCenv hLpos.le) (mul_nonneg hD hcensus))
  unfold canonicalCombinedPowerCorrection
  exact add_nonneg hphysical hguard















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeBaselineL1 -/
section


/-!
# Uniform baseline-to-actual `L¹` control for the paper bridge

The nuisance covariance argument in Lemma 8.4 needs the *actual* tilted
finite law to remain close to the actual finite baseline law throughout a
fixed effective parameter box.  The medium-prime score is not uniformly
small pointwise, so this cannot be proved by a sup-norm estimate alone.

This file proves the needed finite statement from literal arithmetic-cell
data.  A positive cell-density bound gives an `O(sum_{W<p<=y} 1/p / L)`
first absolute moment for the medium valuation score.  The fixed-dimensional
nuisance score contributes `O(1/L)`.  A fixed pointwise score envelope then
converts that first-moment estimate to normalized `L¹` distance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination DivisibilityMomentBounds
open Erdos390.Full.OmittedScoreCell
open Erdos390.Full.PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-! ## Fixed-interval/effective-box specialization -/



/-- A paper-effective ball directly supplies both coefficient bounds used by
the finite `L¹` theorem. -/
theorem effective_bounds_of_paperEffectiveSize
    (xi : B.ParamSpace) {A : ℝ}
    (hbox : B.paperEffectiveSize xi ≤ A) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) ∧
      ‖B.nuisanceParameter xi‖ ≤ A := by
  have hprimeNorm :
      ‖fun p ↦ B.effectivePrimeCoefficient xi p‖ ≤
        B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg (B.nuisanceParameter xi),
      abs_nonneg (xi MomentCoord.slow)]
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤
      B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg
      (fun p ↦ B.effectivePrimeCoefficient xi p),
      abs_nonneg (xi MomentCoord.slow)]
  constructor
  · intro p
    calc
      |B.effectivePrimeCoefficient xi p| ≤
          ‖fun q ↦ B.effectivePrimeCoefficient xi q‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm
            (fun q ↦ B.effectivePrimeCoefficient xi q) p
      _ ≤ B.paperEffectiveSize xi := hprimeNorm
      _ ≤ A := hbox
  · exact hnuisance.trans hbox







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNuisanceUniformFloor -/
section


/-!
# A root uniform lower floor for the canonical nuisance gap

The exact canonical nuisance gap is allowed to use a varying reference head
and a varying positive barycentric target.  This file bounds its two finite
dimensional constants by quantities depending only on the fixed head type,
and replaces the varying cell-mass margin by one prescribed positive floor.
The result is the uniform positive scalar needed before taking an eventual
Schur-smallness threshold.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual nuisance coordinate count is bounded by the full head count
plus the physical coordinate. -/
theorem nuisanceCoord_card_le_head_add_one :
    Fintype.card (NuisanceCoord B.HeadIndex) ≤ Fintype.card Head + 1 := by
  let f : NuisanceCoord B.HeadIndex → Option Head
    | .physical => none
    | .head h => some h.1
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f, Subtype.ext_iff]
  simpa using Fintype.card_le_of_injective f hf

theorem sqrt_nuisanceCoord_card_le_ceiling :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      nuisanceDimensionCeiling Head := by
  unfold nuisanceDimensionCeiling
  apply Real.sqrt_le_sqrt
  exact_mod_cast B.nuisanceCoord_card_le_head_add_one

theorem nuisanceStatisticCoefficient_le_ceiling
    {U : ℝ} (hU : 1 ≤ U) :
    B.nuisanceStatisticCoefficient U ≤
      nuisanceStatisticCoefficientCeiling Head U := by
  unfold nuisanceStatisticCoefficient nuisanceStatisticCoefficientCeiling
  have hmax : 0 ≤ max (PaperStatisticNorm.physicalLogCoefficient U)
      (3 / Real.log 2) := by
    exact (PaperStatisticNorm.physicalLogCoefficient_nonneg hU).trans
      (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    B.sqrt_nuisanceCoord_card_le_ceiling hmax

theorem nuisanceGeometryConstant_le_ceiling (sep R : ℝ) :
    B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R := by
  unfold nuisanceGeometryConstant nuisanceGeometryCeiling
  have hcard : (Fintype.card B.HeadIndex : ℝ) ≤
      (Fintype.card Head : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun h : B.HeadIndex ↦ h.1) (fun _ _ h ↦ Subtype.ext h)
  have hfactor : 0 ≤ 8 * R ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcard hfactor]

omit [DecidableEq Head] in
theorem canonicalEffectiveNuisanceGammaFloor_pos
    (I : PhysicalIntervals) {U a marginFloor : ℝ} {W : ℕ}
    (hmargin : 0 < marginFloor) :
    0 < canonicalEffectiveNuisanceGammaFloor Head I U a W marginFloor := by
  unfold canonicalEffectiveNuisanceGammaFloor
  have hsep := fixedInterval_separation_pos I
  have hgeom : 0 < nuisanceGeometryCeiling Head
      (Real.log (I.lower .plus) - Real.log (I.upper .minus))
      (Real.log U) := by
    unfold nuisanceGeometryCeiling
    positivity
  exact mul_pos (Real.exp_pos _)
    (div_pos (mul_pos (sq_pos_of_pos hmargin) (sq_pos_of_pos hsep))
      (mul_pos (by norm_num) hgeom))

/-- Every target with the prescribed cell-mass floor has a canonical
nuisance gap bounded below by the preceding root scalar. -/
theorem canonicalEffectiveNuisanceGammaFloor_le
    [Nonempty Head]
    (I : PhysicalIntervals) {U a marginFloor : ℝ}
    (hU : 1 ≤ U) (ha : 0 ≤ a) (hmargin : 0 < marginFloor)
    (T : BarycentricTarget B.sampleData)
    (hTmargin : marginFloor ≤ T.cellMassMargin) :
    canonicalEffectiveNuisanceGammaFloor Head I U a B.sampleData.W
        marginFloor ≤
      B.canonicalEffectiveNuisanceGamma I U a T := by
  let sep : ℝ := Real.log (I.lower .plus) - Real.log (I.upper .minus)
  let R : ℝ := Real.log U
  let Kactual : ℝ :=
    PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      B.nuisanceStatisticCoefficient U
  let Kceiling : ℝ :=
    PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      nuisanceStatisticCoefficientCeiling Head U
  have hK : Kactual ≤ Kceiling := by
    dsimp only [Kactual, Kceiling]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hKa : Kactual * a ≤ Kceiling * a :=
    mul_le_mul_of_nonneg_right hK ha
  have hexp : Real.exp (-2 * (Kceiling * a)) ≤
      Real.exp (-2 * (Kactual * a)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsep : 0 < sep := fixedInterval_separation_pos I
  have hTpos : 0 < T.cellMassMargin := T.cellMassMargin_pos
  have hmarginSq : marginFloor ^ 2 ≤ T.cellMassMargin ^ 2 :=
    (sq_le_sq₀ hmargin.le hTpos.le).2 hTmargin
  have hnum : marginFloor ^ 2 * sep ^ 2 ≤
      T.cellMassMargin ^ 2 * sep ^ 2 :=
    mul_le_mul_of_nonneg_right hmarginSq (sq_nonneg sep)
  have hgeomActual : 0 < B.nuisanceGeometryConstant sep R :=
    B.nuisanceGeometryConstant_pos sep R
  have hgeomCeiling : 0 < nuisanceGeometryCeiling Head sep R := by
    unfold nuisanceGeometryCeiling
    positivity
  have hgeomLe : B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R :=
    B.nuisanceGeometryConstant_le_ceiling sep R
  have hgap :
      marginFloor ^ 2 * sep ^ 2 /
          (2 * nuisanceGeometryCeiling Head sep R) ≤
        B.uniformNuisanceGap T.cellMassMargin sep R := by
    unfold uniformNuisanceGap
    exact div_le_div₀
      (mul_nonneg (sq_nonneg T.cellMassMargin) (sq_nonneg sep)) hnum
      (mul_pos (by norm_num) hgeomActual)
      (mul_le_mul_of_nonneg_left hgeomLe (by norm_num))
  have hexp0 : 0 ≤ Real.exp (-2 * (Kceiling * a)) :=
    (Real.exp_pos _).le
  have hgap0 : 0 ≤ B.uniformNuisanceGap T.cellMassMargin sep R := by
    unfold uniformNuisanceGap
    positivity
  have hfloorGap0 : 0 ≤
      marginFloor ^ 2 * sep ^ 2 /
        (2 * nuisanceGeometryCeiling Head sep R) := by positivity
  unfold canonicalEffectiveNuisanceGammaFloor canonicalEffectiveNuisanceGamma
  dsimp only [sep, R, Kactual, Kceiling] at hexp hgap ⊢
  exact mul_le_mul hexp hgap hfloorGap0 (Real.exp_pos _).le

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSquarefreeMarkedRow -/
section


/-!
# The squarefree marked row at the paper's relative scale

This file records the finite row calculation used in Lemma 8.6 and
Proposition 8.7.  A signed product-reciprocal comparison with the
Poisson--Dickman reference matrix is summed against the literal compensated
coefficient.  The result is pointwise in the marked prime and therefore does
not follow from a band-averaged operator estimate.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- Complete squarefree marked-row estimate from signed entry comparison.
The second-reciprocal diagonal term is paid with one explicit `1/W`. -/
theorem actualSquarefreeMarkedRow_le_of_entrywise [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond CF CKernel Csup CL1 w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonDiag : 0 ≤ epsilonDiag)
    (hepsilonSecond : 0 ≤ epsilonSecond)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hCsup : 0 ≤ Csup) (hw : 0 ≤ w)
    (hW : 0 < B.sampleData.W)
    (hcoeffSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ Csup * w)
    (hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          CL1 * w)
    (hentry : ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2
          else 0)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      ((CKernel * CL1 + CF * Csup) +
          (epsilonOff * CL1 + epsilonDiag * Csup +
            epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ)))) *
        w * (1 / (p : ℝ)) := by
  let reference : ℝ :=
    ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
      B.actualCompensatedNatCoefficient q r *
        squarefreeReferenceEntry B.sampleData.n p r
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hWR : (0 : ℝ) < B.sampleData.W := by exact_mod_cast hW
  have hWp : (B.sampleData.W : ℝ) ≤ p := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le
  have hinv : 1 / (p : ℝ) ≤ 1 / (B.sampleData.W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  have hdiff := B.actualSquarefreeMarkedRow_sub_reference_le xi q
    hepsilonOff hcoeffL1 hentry hp
  have href := B.referenceMarkedRow_le q hCF hCKernel
    hcoeffSup hcoeffL1 hF hKernel hp
  have hcp := hcoeffSup p hp
  have hdiagSecond :
      |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) ≤
        (epsilonDiag * Csup +
            epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
          w * (1 / (p : ℝ)) := by
    have hdiagNonneg : 0 ≤ epsilonDiag * (1 / (p : ℝ)) +
        epsilonSecond * (1 / (p : ℝ)) ^ 2 := by positivity
    calc
      _ ≤ (Csup * w) *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hcp hdiagNonneg
      _ ≤ (Csup * w) *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond *
              ((1 / (B.sampleData.W : ℝ)) * (1 / (p : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCsup hw)
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left
            (by
              rw [pow_two]
              exact mul_le_mul_of_nonneg_right hinv
                (one_div_nonneg.mpr hpR.le))
            hepsilonSecond) _
      _ = _ := by ring
  have hdiff' :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q) - reference| ≤
        (epsilonOff * CL1 + epsilonDiag * Csup +
            epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
          w * (1 / (p : ℝ)) := by
    calc
      _ ≤ (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
          |B.actualCompensatedNatCoefficient q p| *
            (epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
        simpa only [reference] using hdiff
      _ ≤ (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
          (epsilonDiag * Csup +
              epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
            w * (1 / (p : ℝ)) := add_le_add_right hdiagSecond _
      _ = _ := by ring
  calc
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| =
      |((B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q) - reference) + reference| := by ring_nf
    _ ≤ |(B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q) - reference| + |reference| :=
      abs_add_le _ _
    _ ≤ (epsilonOff * CL1 + epsilonDiag * Csup +
          epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
          w * (1 / (p : ℝ)) +
        (CKernel * CL1 + CF * Csup) * w * (1 / (p : ℝ)) :=
      add_le_add hdiff' (by simpa only [reference] using href)
    _ = _ := by ring

/-- The canonical signed one- and two-divisor profiles give the literal
actual-law entry comparison.  The equality between the sigma mixture and the
global guarded tilted law keeps all between-cell covariance terms. -/
theorem actualSquarefreeEntry_bound_of_profiles [Nonempty Head]
    (xi : B.ParamSpace) {Eprofile CKernel : ℝ}
    (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hKernelDiag : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            (2 * Eprofile) * (1 / (p : ℝ)) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * (1 / (p : ℝ)) ^ 2
          else 0 := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    SquarefreeCovarianceReference.sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight (B.actualComponentValuationLaw xi) B.n_gt_one
      hpair hsingle hKernelDiag
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  intro p r hp hr
  have h := hraw ⟨p, hp⟩ ⟨r, hr⟩
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hr).ne_zero
  by_cases hpr : p = r
  · subst r
    convert h using 1
    field_simp [hp0]
  · have hsub : (⟨p, hp⟩ : BandPrime B.sampleData.n B.sampleData.W) ≠
        ⟨r, hr⟩ := by
      intro heq
      exact hpr (congrArg Subtype.val heq)
    simp only [if_neg hsub] at h
    convert h using 1
    simp only [if_neg hpr]
    field_simp [hp0, hr0]

/-- Paper-facing squarefree marked row with no abstract row hypothesis.  Its
inputs are exactly the signed local profiles, the two uniform kernel bounds,
and the coefficient estimates already used in the slow quadratic argument. -/
theorem actualSquarefreeMarkedRow_le_of_profiles [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Eprofile CF CKernel : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hEprofile : 0 ≤ Eprofile) (hCF : 0 ≤ CF)
    (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      ((CKernel * (7 + C * K) + CF * (1 + C)) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              (7 + C * K) +
            (2 * Eprofile) * (1 + C) +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * (1 + C) *
              (1 / (B.sampleData.W : ℝ)))) *
        w * (1 / (p : ℝ)) := by
  have hcoeff := B.partition.compensatedCoefficient_three_bounds
    B.n_gt_one q hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hcoeffSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ (1 + C) * w := by
    intro r hr
    rw [B.actualCompensatedNatCoefficient_of_mem q hr]
    simpa only [B.partition_compensatedCoefficient_eq q ⟨r, hr⟩] using
      hcoeff.1 ⟨r, hr⟩
  have hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          (7 + C * K) * w := by
    rw [B.compensatedNatL1_eq_partition q]
    exact hcoeff.2.1
  have hentry := B.actualSquarefreeEntry_bound_of_profiles xi hEprofile
    hpair hsingle (fun r hr ↦ hKernel ⟨r, hr⟩ ⟨r, hr⟩)
  have hCsup : 0 ≤ 1 + C := by positivity
  have hoff : 0 ≤
      4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile :=
    mul_nonneg (by norm_num)
      (PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile)
  have hsecond : 0 ≤
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + CKernel :=
    add_nonneg (sq_nonneg _) hCKernel
  exact B.actualSquarefreeMarkedRow_le_of_entrywise xi q
    hoff (mul_nonneg (by norm_num) hEprofile) hsecond hCF hCKernel
    hCsup hw hW hcoeffSup hcoeffL1 hentry hF hKernel hp

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalActualMomentBoundsEventually -/
section


/-!
# Canonical actual-prime moment bounds, uniformly in the separation proof

`RegularMeshActualMomentBoundsEventually` constructs a partition
existentially.  For the paper-facing bridge we need the same estimates on
the literal canonical partition appearing in the bridge hypothesis, and we
need them for every proof of the scale-separation inequalities.  Proof
irrelevance is not used as an analytic input here: the endpoint inequalities
are established first and the canonical partition is then constructed from
any supplied separation proof.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature





theorem canonicalMassQuadratureBound
    (A Y : ℕ) (hA : canonicalMassQuadratureCutoff ≤ A)
    (hAY : A ≤ Y) :
    |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * canonicalMassQuadratureConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound).2)
    A Y hA hAY





theorem canonicalSecondMomentBound
    (z : ℝ) (hz : 1 < z) (A Y : ℕ)
    (hA : canonicalSecondMomentCutoff ≤ A) (hAY : A ≤ Y) :
    |KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z Y -
        KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
      3 * canonicalSecondMomentConstant /
        (Real.log z ^ 2 * Real.log (A : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound).2)
    z hz A Y hA hAY



namespace Mesh

section DiagonalMomentMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMomentMesh

section GenericFirstMomentMesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The deviation, first-moment, and variance-upper estimates are uniform
for independent mesh parameters `delta` and `eta`.  No variance lower bound,
and hence no comparison `M.ratio ≤ delta`, is used here. -/
theorem canonicalActualPreliminaryMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            delta ^ 2 / 4 ≤ P.bandVariance 0 ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Xmass : ℕ := canonicalMassQuadratureCutoff
  let Cfirst : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : ℝ := canonicalSecondMomentConstant
  let Xsecond : ℕ := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : ℝ) ^ 2 -
            realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
    intro z hz A Y hA hAY
    simpa only [Csecond, Xsecond] using
      canonicalSecondMomentBound z hz A Y hA hAY
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint := eventually_endpointMomentBounds M hdelta W
    Cmass Cfirst Csecond (by omega : 1 < W)
  filter_upwards [hEndpoint] with n R
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hReady := momentReady_of_endpointMomentBounds M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hW8 hXmass hXfirst hXsecond
      hMass hFirst hSecond R
  have hL1 := actual_L1_bound_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hVarUpper := actual_variance_upper_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hLow := actual_low_bandVariance_lower_of_ready M P E
    (fun j ↦ rfl) hdelta hn hReady
  have hSup := actual_deviation_sup_le_scale M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn
  exact ⟨hSup, hL1, hLow, hVarUpper⟩

/-- Generic actual-scale upper-moment interface. -/
theorem canonicalActualUpperMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  intro W hW
  have hPreliminary :=
    canonicalActualPreliminaryMomentCutoff_eventually M hdelta W hW
  filter_upwards [hPreliminary] with n hAt
  obtain ⟨hWne, hn, hAll⟩ := hAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hSup, hL1, _hLow, hVarUpper⟩ := hAll S
  exact ⟨hSup, hL1, hVarUpper⟩







end GenericFirstMomentMesh

section DiagonalMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMesh

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperSelectedMeshSchurRateEventually -/
section


/-!
# Vanishing nuisance-Schur rate at the moving-low scale

This file isolates the rate calculation needed after the selected-mesh
full-band inverse.  A reciprocal nuisance row of size `epsilon n / p`,
with both `epsilon n -> 0` and `epsilon n * log (log n) -> 0`, survives the
moving-low loss `amin = c / log (log n)`: the resulting Schur perturbation
still tends to zero.  All dimension, moment, and nuisance-gap constants are
explicit.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]





/-- A nonnegative row rate whose product with `log (log n)` tends to zero
already tends to zero.  This small lemma lets the analytic marked-row API
expose only its genuinely sharp rate. -/
theorem tendsto_zero_of_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n :=
    Filter.Eventually.of_forall hepsilonNonneg
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hlogOne] with n hn
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hn (hepsilonNonneg n)
  exact squeeze_zero' hlower hupper hepsilonRate









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87MarkedRowRate -/
section


/-!
# Marked-row rates used after the Proposition 8.7 radius is fixed

The ordinary fast target loses the full harmonic mass `O(log L)`, whereas
the compensated slow row has no such loss.  The canonical marked-row rate
was deliberately proved with `epsilon n * log L n -> 0`; this file checks
the two exact eventual estimates and keeps the choice of the ODE radius
strictly before the ambient threshold.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- The literal sum of arithmetic band masses has the global `12 log L`
bound, uniformly over every bridge whose ambient integer and cutoff are the
displayed `n,W`. -/
theorem eventually_sum_harmonicMass_le_twelve_logL (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
          (∑ j : Band, B.harmonicMass j) ≤
            12 * Real.log (Scale.L B.sampleData.n) := by
  filter_upwards [PrimeSums.eventually_bandReciprocalSum_le_logL W]
      with n hn
  intro B hBn hBW
  rw [B.sum_harmonicMass_eq_bandReciprocalSum, hBn, hBW]
  simpa only [hBn] using hn









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualCompensatedMarkedRowProfiles -/
section


/-!
# The compensated slow marked row from literal analytic inputs

This removes two legacy contracts from the marked-row side of Lemma 8.6:
the squarefree marked row is derived from the signed divisor profiles, and
the prime-power correction is supplied by the literal weighted `VV-II` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance
open PaperPrimePowerRelativeQuadratic PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Full compensated marked row, derived from the local signed profiles,
the literal weighted prime-power row, and reciprocal nuisance rows. -/
theorem actualCompensatedScore_markedRow_bound_of_profiles_and_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R Eprofile CF CKernel Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hEprofile : 0 ≤ Eprofile) (hCF : 0 ≤ CF)
    (hCKernel : 0 ≤ CKernel) (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      actualSquarefreeMarkedConstant C K Eprofile CF CKernel
          (1 / (B.sampleData.W : ℝ)) * w * (1 / (p : ℝ)) +
        (1 + C) * w * R * (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * w * (1 / (p : ℝ)) := by
  have hsquarefree := B.actualSquarefreeMarkedRow_le_of_profiles
    xi q hC hw hEprofile hCF hCKernel hW hsharp hbandT hdevSup hdevL1
      hdevL2 hpair hsingle hF hKernel hp
  have hsquarefree' :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q)| ≤
        actualSquarefreeMarkedConstant C K Eprofile CF CKernel
            (1 / (B.sampleData.W : ℝ)) * w * (1 / (p : ℝ)) := by
    simpa only [actualSquarefreeMarkedConstant, add_assoc] using hsquarefree
  have hpower := B.actual_primePower_relative_markedRow_bound_of_row
    xi q hC hw hsharp hbandT hdevSup hdevL1 hdevL2 hrow hp
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZ :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  have hmarkedCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p (B.sampleData.value m))| ≤
          Cmarked * (1 / (p : ℝ)) := fun c ↦ hmarked c ⟨p, hp⟩
  have hmarkedZ : ‖B.nuisanceCovarianceVector xi
      (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        Cmarked) * (1 / (p : ℝ)) := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (fun m ↦ valuation p (B.sampleData.value m))
      (mul_nonneg hCmarked (by positivity)) hmarkedCoord
    simpa only [mul_assoc] using hraw
  have hnuisance := B.actualNuisanceCoefficient_markedRow_bound
    xi hgamma hgap q (fun m ↦ valuation p (B.sampleData.value m))
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg hCmarked (by positivity))) hw hcovZ hmarkedZ
  let fitted := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.actualCompensatedScore xi hgamma hgap q)
  let full := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.postBandPrimeScore q)
  let squarefree := (B.tiltedLaw xi).covariance
    (fun m ↦ divInd p (B.sampleData.value m))
    (B.postBandSquarefreeScore q)
  let nuisance := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (fun m ↦ inner ℝ
      (B.actualNuisanceCoefficient xi hgamma hgap q)
      (B.nuisanceStatistic m))
  have hdecomp : fitted = full - nuisance := by
    exact B.actualCompensatedScore_markedRow_decomposition
      xi hgamma hgap q p
  have hfull : |full| ≤ |full - squarefree| + |squarefree| := by
    calc
      |full| = |(full - squarefree) + squarefree| := by ring_nf
      _ ≤ |full - squarefree| + |squarefree| := abs_add_le _ _
  calc
    |fitted| = |full - nuisance| := by rw [hdecomp]
    _ ≤ |full| + |nuisance| := abs_sub _ _
    _ ≤ (|full - squarefree| + |squarefree|) + |nuisance| :=
      add_le_add hfull le_rfl
    _ ≤ ((1 + C) * w * R * (1 / (p : ℝ)) +
          actualSquarefreeMarkedConstant C K Eprofile CF CKernel
            (1 / (B.sampleData.W : ℝ)) * w * (1 / (p : ℝ))) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * w * (1 / (p : ℝ)) :=
      add_le_add (add_le_add hpower hsquarefree') hnuisance
    _ = _ := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87MarkedTwoStage -/
section


/-!
# Marked rows for the literal two-stage Proposition 8.7 solve

This file removes the last algebraic indirection between the two rows
estimated in the paper and the marked row of the actual ODE vector field.
The fast row is evaluated at the inverse solution of the projected target;
the slow row is evaluated at the compensated regression score.  The exact
Schur equation supplies their coefficients, and the proved compensated
variance bound controls the slow coefficient.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Assemble the marked row of the actual vector field from the literal
fast and compensated-slow rows.

There is no assumed vector-field row in this theorem.  The identity of the
fast coordinate, the coefficient of the compensated score, and the bound
on that coefficient are all consequences of the exact Schur solve. -/
theorem vectorField_markedRow_le_of_twoStage_rows
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q =
      B.actualBandSchurLinearMap xi hgammaNuisance hGamma q)
    (p : ℕ) {Vlower Tslow Cfast Cslow rho : ℝ}
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hvariance : Vlower ≤
      B.actualTwoStageCompensatedVariance
        xi hgammaNuisance hGamma e)
    (htarget : |B.compensatedNormalizedTarget
      xi hgammaNuisance hGamma e Delta| ≤ Tslow)
    (hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore
            (e.symm (B.projectedNormalizedTargetBand Delta))))| ≤
        Cfast * rho)
    (hcompensated :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)| ≤
        (Cslow * rho) * B.w) :
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (Cfast + (Tslow / Vlower) * (Cslow * B.w)) * rho := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let qFast := e.symm (B.projectedNormalizedTargetBand Delta)
  let qReg := B.actualBandRegression xi hgammaNuisance hGamma e
  let lambda := u MainCoord.slow / B.w
  have hu : B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
      B.mainPart (B.normalizedTarget Delta) := by
    simpa only [u, v] using
      (B.vectorField_eq_schurResidual_and_mainEquation
        xi Delta hgammaFull hFull hgammaNuisance hGamma).2
  have hfastEq : B.fastGaugeOfMain
      xi hgammaNuisance hGamma e u = qFast := by
    simpa only [qFast] using
      B.fastGauge_eq_inverse_projectedTarget
        xi hgammaNuisance hGamma e he Delta u hu
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    rw [← hfastEq]
    simpa only [lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression
        xi hgammaNuisance hGamma e u
  have hstored : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hlambda : |lambda| ≤ Tslow / Vlower := by
    simpa only [lambda] using
      B.abs_slow_div_le_of_variance_target_bounds
        xi hgammaNuisance hGamma e he Delta u hu
          hVlower hvariance hTslow htarget
  have hstoredNonneg : 0 ≤ B.w * (Tslow / Vlower) := by
    exact mul_nonneg B.w_pos.le (div_nonneg hTslow hVlower.le)
  have hlambdaStored :
      |lambda| ≤ (B.w * (Tslow / Vlower)) / B.w := by
    convert hlambda using 1
    field_simp [B.w_pos.ne']
  have hcompensated' :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualCompensatedScore
          xi hgammaNuisance hGamma qReg)| ≤
        (Cslow * rho) * B.w := by
    simpa only [qReg, actualTwoStageCompensatedScore] using hcompensated
  have hrow :=
    B.vectorField_markedRow_le_of_fast_compensated
      xi Delta hgammaFull hFull hgammaNuisance hGamma
      p qFast qReg lambda hstoredNonneg hq hstored hfast
      hcompensated' hlambdaStored
  have hrow' := hrow.trans_eq (show
      (Cfast + (B.w * (Tslow / Vlower)) * Cslow) * rho =
        (Cfast + (Tslow / Vlower) * (Cslow * B.w)) * rho by ring)
  simpa only [qFast, qReg, lambda, v, u] using hrow'

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87MarkedProfilesAssembly -/
section


/-!
# Proposition 8.7 marked row from literal profile inputs

This file composes the two independently proved component rows with the
exact two-stage Schur solve.  In particular, neither component marked row
nor the marked row of the ODE vector field is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- Literal finite marked-row conclusion for the Proposition 8.7 vector
field.  The only inputs are the analytic profile/kernel/prime-power rows,
the two inverse/target estimates, and the exact covariance gaps. -/
theorem vectorField_markedRow_le_of_profiles_and_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q =
      B.actualBandSchurLinearMap xi hgammaNuisance hGamma q)
    {Vlower Tslow CinvOrd Tband Creg : ℝ}
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCinvOrd : 0 ≤ CinvOrd)
    (hCreg : 0 ≤ Creg)
    (hvariance : Vlower ≤
      B.actualTwoStageCompensatedVariance xi hgammaNuisance hGamma e)
    (htarget : |B.compensatedNormalizedTarget
      xi hgammaNuisance hGamma e Delta| ≤ Tslow)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    {H K Eprofile CF Cprod CKernel R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hK : 0 ≤ K) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgammaNuisance hGamma e) ≤ Creg * B.w)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernelProduct : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (fastProfilesMarkedConstant
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
          H K Eprofile CF Cprod R Cmarked gammaNuisance
          (1 / (B.sampleData.W : ℝ)) * (CinvOrd * Tband) +
        (Tslow / Vlower) *
          (slowProfilesMarkedConstant
            (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
            Creg K R Eprofile CF CKernel Cmarked gammaNuisance
            (1 / (B.sampleData.W : ℝ)) * B.w)) *
        (1 / (p : ℝ)) := by
  let dimension : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let CfastBase : ℝ := fastProfilesMarkedConstant dimension H K Eprofile
    CF Cprod R Cmarked gammaNuisance (1 / (B.sampleData.W : ℝ))
  let Cslow : ℝ := slowProfilesMarkedConstant dimension Creg K R
    Eprofile CF CKernel Cmarked gammaNuisance
      (1 / (B.sampleData.W : ℝ))
  let qFast := e.symm (B.projectedNormalizedTargetBand Delta)
  let qSlow := B.actualBandRegression xi hgammaNuisance hGamma e
  have hpairScale :=
    PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile
  have hCfastBase : 0 ≤ CfastBase := by
    dsimp only [CfastBase, fastProfilesMarkedConstant, dimension]
    positivity
  have hqFast : ‖qFast‖ ≤ CinvOrd * Tband := by
    calc
      ‖qFast‖ ≤ CinvOrd * ‖B.projectedNormalizedTargetBand Delta‖ :=
        hinvOrd _
      _ ≤ CinvOrd * Tband :=
        mul_le_mul_of_nonneg_left htargetBand hCinvOrd
  have hfastRaw :=
    B.nuisanceResidual_bandRegression_markedRow_le_of_profiles
      xi hgammaNuisance hGamma qFast hH0 hCmarked hEprofile hCprod
        hW hH hbandT hpair hsingle hF hKernelProduct hrow hmarked hp
  have hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore qFast))| ≤
        (CfastBase * (CinvOrd * Tband)) * (1 / (p : ℝ)) := by
    have hscale : CfastBase * ‖qFast‖ * (1 / (p : ℝ)) ≤
        CfastBase * (CinvOrd * Tband) * (1 / (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqFast hCfastBase) (by positivity)
    have hraw :
        |(B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore qFast))| ≤
          CfastBase * ‖qFast‖ * (1 / (p : ℝ)) := by
      simpa only [CfastBase, dimension, fastProfilesMarkedConstant] using
        hfastRaw
    simpa only [markedValuation] using hraw.trans hscale
  have hslowRaw :=
    B.actualCompensatedScore_markedRow_bound_of_profiles_and_weightedRow
      xi qSlow hCreg hK B.w_pos.le hEprofile hCF hCKernel hCmarked
        hW hsharp hbandT hdevSup hdevL1 hdevL2 hgammaNuisance hGamma
        hpair hsingle hF hKernel hrow hmarked hp
  have hslow :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)| ≤
        (Cslow * (1 / (p : ℝ))) * B.w := by
    have hraw :
        |(B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.actualCompensatedScore xi hgammaNuisance hGamma qSlow)| ≤
          (Cslow * (1 / (p : ℝ))) * B.w := by
      calc
        _ ≤ actualSquarefreeMarkedConstant Creg K Eprofile CF CKernel
              (1 / (B.sampleData.W : ℝ)) * B.w * (1 / (p : ℝ)) +
            (1 + Creg) * B.w * R * (1 / (p : ℝ)) +
            (((dimension * (Cmarked * (7 + Creg * K))) /
                gammaNuisance) * (dimension * Cmarked)) * B.w *
                  (1 / (p : ℝ)) := by
          simpa only [qSlow, dimension] using hslowRaw
        _ = (Cslow * (1 / (p : ℝ))) * B.w := by
          simp only [Cslow, slowProfilesMarkedConstant]
          ring
    simpa only [markedValuation, actualTwoStageCompensatedScore, qSlow]
      using hraw
  have hassembled := B.vectorField_markedRow_le_of_twoStage_rows
    xi Delta hgammaFull hFull hgammaNuisance hGamma e he p hVlower
      hTslow hvariance htarget hfast hslow
  simpa only [qFast, CfastBase, Cslow, dimension] using hassembled

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87UniformMarkedProfiles -/
section


/-!
# Uniform Proposition 8.7 marked rows on a preselected effective ball

This is the exact quantifier wrapper used by the ODE theorem.  It turns the
literal analytic inputs, uniform on a previously selected ball, into the
single marked-row estimate expected by the integration argument.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- Uniform marked row on the exact preselected ODE ball.  The monitored
set is explicitly required to lie in the moving prime band; fixed head
primes are handled by their exact head coordinates instead. -/
theorem uniform_vectorField_markedRow_on_effectiveBall_of_profiles
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (a : NNReal)
    {gammaFull gammaNuisance Vlower Tslow CinvOrd Tband Creg : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hgammaNuisance : 0 < gammaNuisance)
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hCinvOrd : 0 ≤ CinvOrd) (hCreg : 0 ≤ Creg)
    (hFull : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull (B.effectiveParamEquiv z))
    (hGamma : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ), ∀ v,
      gammaNuisance * ‖v‖ ^ 2 ≤ inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v))
    (e : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      e z hz q = B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
        hgammaNuisance
        (by
          intro v
          exact hGamma z hz v) q)
    (hvariance : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      Vlower ≤ B.actualTwoStageCompensatedVariance
        (B.effectiveParamEquiv z) hgammaNuisance
        (by intro v; exact hGamma z hz v) (e z hz))
    (htarget : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
        hgammaNuisance (by intro v; exact hGamma z hz v)
        (e z hz) Delta| ≤ Tslow)
    (hinvOrd : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    {H K Eprofile CF Cprod CKernel R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hK : 0 ≤ K) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked) (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hsharp : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression (B.effectiveParamEquiv z)
          hgammaNuisance (by intro v; exact hGamma z hz v) (e z hz)) ≤
        Creg * B.w)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hpair : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw
              (B.effectiveParamEquiv z) c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw
              (B.effectiveParamEquiv z) c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernelProduct : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    (hrow : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (r : BandPrime B.sampleData.n B.sampleData.W),
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw (B.effectiveParamEquiv z)).covVV r.1 s.1 -
            (B.actualValuationLaw (B.effectiveParamEquiv z)).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    (monitoredPrimes : Finset ℕ)
    (hmonitored : ∀ p ∈ monitoredPrimes,
      p ∈ primeBand B.sampleData.n B.sampleData.W) :
    ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
            (B.markedValuation p)
            (fun m ↦ B.vectorFamily.scalarFamily.score m
              (B.vectorFamily.vectorField (B.targetVector Delta)
                (B.effectiveParamEquiv z)))
            (B.effectiveParamEquiv z)| ≤
          B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod CKernel
            R Cmarked gammaNuisance CinvOrd Tband Tslow Vlower Creg /
              (p : ℝ) := by
  intro p hp z hz
  let hGapZ : ∀ v, gammaNuisance * ‖v‖ ^ 2 ≤
      inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) :=
    fun v ↦ hGamma z hz v
  have hfinite := B.vectorField_markedRow_le_of_profiles_and_weightedRow
    (B.effectiveParamEquiv z) Delta hgammaFull (hFull z hz)
      hgammaNuisance hGapZ (e z hz)
      (by intro q; simpa only [hGapZ] using he z hz q)
      hVlower hTslow hCinvOrd hCreg
      (by simpa only [hGapZ] using hvariance z hz)
      (by simpa only [hGapZ] using htarget z hz)
      (hinvOrd z hz) htargetBand hH0 hK hEprofile hCF hCprod hCKernel
      hR hCmarked hW hH hbandT
      (by simpa only [hGapZ] using hsharp z hz)
      hdevSup hdevL1 hdevL2 (hpair z hz) (hsingle z hz) hF
      hKernelProduct hKernel (hrow z hz) (hmarked z hz) (hmonitored p hp)
  simpa only [vectorFieldProfilesMarkedConstant, div_eq_mul_inv, one_mul]
    using hfinite

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87MarkedProfilesMajorant -/
section


/-!
# An ambient-independent majorant for the Proposition 8.7 marked row

The signed-profile and nuisance errors are `o(1 / log L)`, while the total
harmonic mass is `O(log L)`.  This file records the exact finite inequality
which converts those rates into one constant independent of the ambient
integer.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

set_option maxHeartbeats 1200000

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- Exact cancellation lemma used by the paper-order Proposition 8.7
terminal.  Its right side contains no occurrence of `B.w`. -/
theorem vectorFieldProfilesMarkedConstant_le_scaledMajorant
    {H K Eprofile CF Cprod CKernel R Rmax Cmarked gammaNuisance
      gammaFloor CinvOrd Tband targetScale gammaSlow Creg : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hE : 0 ≤ Eprofile) (hEone : Eprofile ≤ 1)
    (hEH : Eprofile * H ≤ 1)
    (hCF : 0 ≤ CF) (hCprod : 0 ≤ Cprod)
    (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R) (hRRmax : R ≤ Rmax)
    (hM : 0 ≤ Cmarked) (hMone : Cmarked ≤ 1)
    (hMH : Cmarked * H ≤ 1)
    (hgammaFloor : 0 < gammaFloor)
    (hgamma : 0 < gammaNuisance)
    (hgammaCompare : gammaFloor ≤ gammaNuisance)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTargetScale : 0 ≤ targetScale) (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg) (hW : 1 < B.sampleData.W) :
    B.vectorFieldProfilesMarkedConstant H K Eprofile CF Cprod CKernel R
        Cmarked gammaNuisance CinvOrd Tband (B.w * targetScale)
          (gammaSlow * B.w ^ 2) Creg ≤
      B.vectorFieldProfilesMarkedScaledMajorant K CF Cprod CKernel Rmax
        gammaFloor CinvOrd Tband targetScale gammaSlow Creg := by
  have hraw := B.vectorFieldProfilesMarkedConstant_le_majorant
    hH hK hE hEone hEH hCF hCprod hCKernel hR hRRmax hM hMone hMH
      hgammaFloor hgamma hgammaCompare hCinvOrd hTband
      (mul_nonneg B.w_pos.le hTargetScale)
      (mul_pos hgammaSlow (sq_pos_of_pos B.w_pos)) hCreg hW
  calc
    _ ≤ B.vectorFieldProfilesMarkedMajorant K CF Cprod CKernel Rmax
          gammaFloor CinvOrd Tband (B.w * targetScale)
            (gammaSlow * B.w ^ 2) Creg := hraw
    _ = B.vectorFieldProfilesMarkedScaledMajorant K CF Cprod CKernel Rmax
          gammaFloor CinvOrd Tband targetScale gammaSlow Creg := by
      unfold vectorFieldProfilesMarkedMajorant
        vectorFieldProfilesMarkedScaledMajorant
      field_simp [B.w_pos.ne', hgammaSlow.ne']



/-- The datum-dependent scaled majorant is bounded by the single constant
chosen from the finite head type.  This is the formal uniformity statement
needed to move `∃ Crow` outside the eventual ambient quantifier. -/
theorem vectorFieldProfilesMarkedScaledMajorant_le_headMajorant
    {K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband
      targetScale gammaSlow Creg : ℝ}
    (hK : 0 ≤ K)
    (hgammaFloor : 0 < gammaFloor)
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hTargetScale : 0 ≤ targetScale) (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg) :
    B.vectorFieldProfilesMarkedScaledMajorant K CF Cprod CKernel Rmax
        gammaFloor CinvOrd Tband targetScale gammaSlow Creg ≤
      vectorFieldProfilesMarkedScaledHeadMajorant Head K CF Cprod CKernel
        Rmax gammaFloor CinvOrd Tband targetScale gammaSlow Creg := by
  let d2 : ℝ :=
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let D2 : ℝ := (Fintype.card Head + 1 : ℝ)
  have hd2 : 0 ≤ d2 := by dsimp only [d2]; positivity
  have hD2 : 0 ≤ D2 := by dsimp only [D2]; positivity
  have hdim : d2 ≤ D2 := by
    dsimp only [d2, D2]
    exact_mod_cast B.nuisanceCoord_card_le_head_add_one
  have hsqrt :
      (Real.sqrt
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 = d2 := by
    dsimp only [d2]
    exact Real.sq_sqrt (by positivity)
  have hdiv : d2 / gammaFloor ≤ D2 / gammaFloor :=
    div_le_div_of_nonneg_right hdim hgammaFloor.le
  have hS : 0 ≤ 7 + Creg * K := by positivity
  have hdivS : d2 * (7 + Creg * K) / gammaFloor ≤
      D2 * (7 + Creg * K) / gammaFloor := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdim hS) hgammaFloor.le
  have hfastMul : 0 ≤ CinvOrd * Tband :=
    mul_nonneg hCinvOrd hTband
  have hslowMul : 0 ≤ targetScale / gammaSlow :=
    div_nonneg hTargetScale hgammaSlow.le
  unfold vectorFieldProfilesMarkedScaledMajorant
    vectorFieldProfilesMarkedScaledHeadMajorant
  dsimp only [D2]
  rw [hsqrt]
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (add_le_add_right hdiv _) hfastMul)
    (mul_le_mul_of_nonneg_left
      (add_le_add_right hdivS _) hslowMul)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86Eventually -/
section


/-!
# Canonical eventual Lemma 8.6 up to the Lemma 8.4 splice

All inputs specific to the slow-variance proof are discharged here:

* actual prime moments and the moving-low relative normalization;
* a positive interior anchor block and the relative row residual;
* full signed component profiles;
* the actual weighted prime-power row through the raw reference law; and
* the finite nuisance marked rows and their uniform positive gap.

The only two displayed call-site estimates are the sharp inverse supplied by
Lemma 8.4 and the normalized slow right column.  They are left as explicit
arguments rather than hidden in a structure.  The cutoff `W` is selected
before the effective ball; all ball dependence enters only the eventual
ambient threshold.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open RegularMeshPrimeCutoffs
open PaperCanonicalSlowKappa

namespace BridgeData

/-- A product-log rate together with eventual nonnegativity implies ordinary
convergence to zero.  This version is convenient for explicit arithmetic
remainders which are only meaningful after the ambient threshold. -/
theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hepsilonNonneg, hlogOne] with n he hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn he
  exact squeeze_zero' hepsilonNonneg hupper hepsilonRate



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalMarkedProfilesEventually -/
section


/-!
# Canonical eventual moving-prime row for Proposition 8.7

All signed-profile, prime-power, nuisance, kernel, harmonic-mass, and regular
mesh inputs are selected here.  The only remaining call-site assumptions are
the exact same-map Schur solve and its ordinary/slow quantitative outputs.
Fixed head primes are intentionally outside this theorem.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

/-! The cutoff is independent of the regular mesh.  Keeping it as a named
object makes the paper quantifier order visible in the exported statement:
`W` is fixed before the head data, the mesh, and the ODE ball. -/


set_option maxHeartbeats 3000000 in
/-- Canonical eventual `C/p` row on the preselected effective ball.  The
universal cutoff is chosen before the head type and head patterns; after a
permitted `W` is fixed, those patterns and then the ODE ball are quantified.
The final ambient threshold may depend on all of that already selected
finite data. -/
theorem exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
    (I : PhysicalIntervals) (U : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {CinvOrd Tband targetScale gammaSlow Creg : ℝ},
      0 ≤ CinvOrd → 0 ≤ Tband → 0 ≤ targetScale →
      0 < gammaSlow → 0 ≤ Creg →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          (hBn : B.sampleData.n = n) →
          (hBW : B.sampleData.W = W) →
          (hBWlarge : 1 < B.sampleData.W) →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
                B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (Delta : Fin (M.cellCount + 1) → ℝ),
            ∀ (T : BarycentricTarget B.sampleData),
              (hTmargin : marginFloor ≤ T.cellMassMargin) →
              (hbaseline : B.baseline = T.baseline) →
              ∀ {gammaFull : ℝ}, 0 < gammaFull →
              (hFull : ∀ z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ),
                B.vectorFamily.HasCovarianceGap gammaFull
                  (B.effectiveParamEquiv z)) →
              ∀ (e : ∀ (z : B.EffectiveParamSpace),
                z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                  B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
              (he : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                e z hz q = B.actualBandSchurLinearMap
                  (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) q) →
              (hvariance : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                gammaSlow * B.w ^ 2 ≤ B.actualTwoStageCompensatedVariance
                  (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) (e z hz)) →
              (htarget : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                  (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) (e z hz) Delta| ≤
                    B.w * targetScale) →
              (hinvOrd : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖) →
              (htargetBand :
                ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband) →
              (hsharp : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                paperSharpNorm B.harmonicMass B.bandCenter
                  (B.partition.center_ne_zero B.n_gt_one)
                  (B.actualBandRegression (B.effectiveParamEquiv z)
                    (B.canonicalEffectiveNuisanceGamma_pos
                      I U (3 * (a : ℝ)) T)
                    (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                      hlowerOne hupperU
                      (by intro sigma; rw [hcanonical]; rfl)
                      (by intro sigma; rw [hcanonical]; rfl)
                      T hbaseline hBWlarge z hz) (e z hz)) ≤ Creg * B.w) →
              ∀ (monitoredPrimes : Finset ℕ),
                (∀ p ∈ monitoredPrimes,
                  p ∈ primeBand B.sampleData.n B.sampleData.W) →
                ∀ p ∈ monitoredPrimes,
                  ∀ z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ),
                  |B.vectorFamily.scalarFamily.covariance
                    (B.markedValuation p)
                    (fun m ↦ B.vectorFamily.scalarFamily.score m
                      (B.vectorFamily.vectorField
                        (B.targetVector Delta)
                        (B.effectiveParamEquiv z)))
                    (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ) := by
  obtain ⟨Cprod, hCprod, hProduct⟩ := DickmanBasic.kernel_product_bound
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  let W₀ := canonicalMovingPrimeMarkedRowCutoff
  refine ⟨W₀, ?_⟩
  intro W hWcut CinvOrd Tband targetScale gammaSlow Creg hCinvOrd
    hTband hTargetScale hgammaSlow hCreg
    Head instFintype instDecidable instNonempty Phead
    hHeadLe a marginFloor hmarginFloor
  have hWone : 1 < W := by
    have : 2 ≤ W := (le_max_left 2
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff).trans hWcut
    omega
  have hWgeom : RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W :=
    (le_max_right 2
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff).trans hWcut
  let CF : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  have hCF : 0 ≤ CF := by
    dsimp only [CF]
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let Rmax : ℝ := Cpow * (1 / (W : ℝ)) + 2
  have hRmax : 0 ≤ Rmax := by
    dsimp only [Rmax]
    positivity
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let Crow : ℝ :=
    vectorFieldProfilesMarkedScaledHeadMajorant Head K CF Cprod Cprod
      Rmax gammaFloor CinvOrd Tband targetScale gammaSlow Creg
  have hCrow : 0 ≤ Crow := by
    dsimp only [Crow, vectorFieldProfilesMarkedScaledHeadMajorant]
    have hA : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    positivity
  refine ⟨Crow, hCrow, ?_⟩
  intro delta eta hdelta M
  obtain ⟨_hCpowTerminal, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe Acoef Aphys hAcoef hAphys
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hWone hHeadLe a
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hUstrict : 1 < U :=
    (hlowerOne .minus).trans_lt
      ((I.lower_lt_upper .minus).trans_le (hupperU .minus))
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hUstrict.le hAphys hWone hn
  have hcombinedT : Tendsto combined atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero
      combined hcombinedNonneg hcombinedRate
  have hprofileOne : ∀ᶠ n : ℕ in atTop, profileError n ≤ 1 :=
    hprofileT.eventually (eventually_le_nhds (by norm_num))
  have hprofileProduct : ∀ᶠ n : ℕ in atTop,
      12 * (profileError n * Real.log (Scale.L n)) ≤ 1 := by
    have ht : Tendsto
        (fun n : ℕ ↦ 12 *
          (profileError n * Real.log (Scale.L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hprofileRate
    exact ht.eventually (eventually_le_nhds (by norm_num))
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero markedError hmarked0 hmarkedRate
  have hmarkedOne : ∀ᶠ n : ℕ in atTop, markedError n ≤ 1 :=
    hmarkedT.eventually (eventually_le_nhds (by norm_num))
  have hmarkedProduct : ∀ᶠ n : ℕ in atTop,
      12 * (markedError n * Real.log (Scale.L n)) ≤ 1 := by
    have ht : Tendsto
        (fun n : ℕ ↦ 12 *
          (markedError n * Real.log (Scale.L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hmarkedRate
    exact ht.eventually (eventually_le_nhds (by norm_num))
  have hepsilonOne : ∀ᶠ n : ℕ in atTop, epsilon75 n ≤ 1 :=
    hepsilon75T.eventually (eventually_le_nhds (by norm_num))
  have hcombinedOne : ∀ᶠ n : ℕ in atTop, combined n ≤ 1 :=
    hcombinedT.eventually (eventually_le_nhds (by norm_num))
  have hlogL0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Scale.L n) := by
    have htop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
        atTop atTop :=
      Real.tendsto_log_atTop.comp (by
        simpa only [Scale.L] using
          Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact htop.eventually (eventually_ge_atTop 0)
  have hgeomN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualUpperMomentCutoff_eventually
      M hdelta W hWgeom
  have hmassN := eventually_sum_harmonicMass_le_twelve_logL
    (Head := Head) (Band := Fin (M.cellCount + 1)) W
  have hbandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hprofileOne, hprofileProduct, hmarkedOne,
    hmarkedProduct, hepsilonOne, hcombinedOne, hcombinedNonneg, hlogL0,
    hgeomN, hmassN, hbandTN, eventually_ge_atTop Nprofile,
    eventually_ge_atTop Npower, eventually_ge_atTop Nmarked] with
      n hprofileOneN hprofileProductN hmarkedOneN hmarkedProductN
      hepsilonOneN hcombinedOneN hcombinedNonnegN hlogL0N hgeomAt
      hmassAt hbandTAt hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition hscale
    Delta T hTmargin hbaseline gammaFull hgammaFull hFull e he hvariance
    htarget hinvOrd htargetBand hsharp monitoredPrimes hmonitored
  subst n
  subst W
  obtain ⟨hWneGeom, hnGeom, hgeomAll⟩ := hgeomAt
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  have hpartitionCanonical : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
        hnGeom hWneGeom S := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw, hdevL2Raw⟩ := hgeomAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    intro p
    rw [hpartitionCanonical]
    calc
      |(RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hnGeom
          hWneGeom S).deviation p| ≤ delta + M.ratio := hdevSupRaw p
      _ ≤ delta + eta := add_le_add_right M.ratio_le_eta delta
      _ = B.w := hscale.symm
  have hdevL1 : B.partition.totalL1 ≤ 7 * B.w := by
    rw [hpartitionCanonical]
    calc
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hnGeom
          hWneGeom S).totalL1 ≤ 7 * (delta + M.ratio) := hdevL1Raw
      _ ≤ 7 * (delta + eta) := by
        gcongr
        exact M.ratio_le_eta
      _ = 7 * B.w := by rw [hscale]
  have hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2 := by
    rw [hpartitionCanonical]
    have hactualNonneg : 0 ≤ delta + M.ratio := by
      linarith [M.ratio_pos]
    have hpaperNonneg : 0 ≤ delta + eta :=
      hactualNonneg.trans (add_le_add_right M.ratio_le_eta delta)
    calc
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hnGeom
          hWneGeom S).variance ≤ 4 * (delta + M.ratio) ^ 2 := hdevL2Raw
      _ ≤ 4 * (delta + eta) ^ 2 := by
        gcongr
        exact M.ratio_le_eta
      _ = 4 * B.w ^ 2 := by rw [hscale]
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  have heta : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |B.effectivePrimeCoefficient (B.effectiveParamEquiv z) p| ≤ Acoef := by
    intro z hz p
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ Acoef := by
      dsimp only [Acoef]
      exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
        (mul_le_mul_of_nonneg_left hznorm (by norm_num))
    exact (B.effective_bounds_of_paperEffectiveSize
      (B.effectiveParamEquiv z) hsize).1 p
  have hphys : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      |B.effectiveParamEquiv z MomentCoord.physical| ≤ Aphys := by
    intro z hz
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ Acoef := by
      dsimp only [Acoef]
      exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
        (mul_le_mul_of_nonneg_left hznorm (by norm_num))
    have hnuisance := (B.effective_bounds_of_paperEffectiveSize
      (B.effectiveParamEquiv z) hsize).2
    calc
      |B.effectiveParamEquiv z MomentCoord.physical| =
          ‖B.nuisanceParameter (B.effectiveParamEquiv z)
            NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ :=
        PiLp.norm_apply_le _ _
      _ ≤ Aphys := by simpa only [Acoef, Aphys] using hnuisance
  have hprofiles : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
      (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
        ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
        |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
            (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
              ((B.actualComponentValuationLaw
                (B.effectiveParamEquiv z) c).value omega)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
            (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
          profileError B.sampleData.n *
            PaperPrimePowerChamberError.pairWeight p r 1 1) ∧
      (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
        |(B.actualComponentValuationLaw (B.effectiveParamEquiv z) c).probability.expect
            (fun omega ↦ divInd p
              ((B.actualComponentValuationLaw
                (B.effectiveParamEquiv z) c).value omega)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
            profileError B.sampleData.n *
              PaperPrimePowerChamberError.singleWeight p 1) := by
    intro z hz
    exact hprofile B (B.effectiveParamEquiv z) hnProfile hPattern hlo hhi
      hGuards (heta z hz) (hphys z hz) rfl
  let R : ℝ := Cpow * (1 / (B.sampleData.W : ℝ)) +
    epsilon75 B.sampleData.n + combined B.sampleData.n
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedNonnegN
  have hRRmax : R ≤ Rmax := by
    dsimp only [R, Rmax]
    linarith
  have hactualRow : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (p : BandPrime B.sampleData.n B.sampleData.W),
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw (B.effectiveParamEquiv z)).covVV p.1 r.1 -
            (B.actualValuationLaw (B.effectiveParamEquiv z)).covII p.1 r.1| ≤ R := by
    intro z hz p
    have hraw := hpower B (B.effectiveParamEquiv z) hnPower rfl
      hsep hremaining hcanonical (heta z hz) (hphys z hz) p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using hraw
  have hmarkedRows : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro z hz c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF := by
    intro p
    have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have harg : DickmanBasic.U - tPrime B.sampleData.n p.1 ∈
        Set.Icc (1 : ℝ) 5 := by
      constructor <;> norm_num [DickmanBasic.U] <;> linarith
    have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by norm_num
    have hrho : DickmanBasic.rho
        (DickmanBasic.U - tPrime B.sampleData.n p.1) ≤ 1 := by
      simpa only [DickmanBasic.rho_one] using
        DickmanBasic.antitoneOn_rho_one_five hone harg (by
          norm_num [DickmanBasic.U]
          linarith)
    rw [abs_of_pos (DickmanBasic.F_pos ⟨ht0, ht1.trans (by norm_num)⟩)]
    unfold DickmanBasic.F
    exact (div_le_div_iff_of_pos_right DickmanBasic.rho_U_pos).2 hrho
  have hKernelProduct : ∀ p r :
      BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n r.1 := by
    intro p r
    exact hProduct _ ⟨
      PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one p.2,
      PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one p.2⟩ _ ⟨
      PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one r.2,
      PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one r.2⟩
  have hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤
        Cprod := by
    intro p r
    have hp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one p.2
    have hp1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have hr0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
      B.n_gt_one r.2
    have hr1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one r.2
    have hprod : tPrime B.sampleData.n p.1 *
        tPrime B.sampleData.n r.1 ≤ 1 := by
      calc
        tPrime B.sampleData.n p.1 * tPrime B.sampleData.n r.1 ≤
            1 * tPrime B.sampleData.n r.1 :=
          mul_le_mul_of_nonneg_right hp1 hr0
        _ ≤ 1 := by simpa using hr1
    calc
      _ ≤ Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n r.1 := hKernelProduct p r
      _ = Cprod * (tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n r.1) := by ring
      _ ≤ Cprod * 1 := mul_le_mul_of_nonneg_left hprod hCprod.le
      _ = Cprod := by ring
  let H : ℝ := 12 * Real.log (Scale.L B.sampleData.n)
  have hH0 : 0 ≤ H := mul_nonneg (by norm_num) hlogL0N
  have hH : (∑ j : Fin (M.cellCount + 1), B.harmonicMass j) ≤ H := by
    simpa only [H] using hmassAt B rfl rfl
  have hEH : profileError B.sampleData.n * H ≤ 1 := by
    dsimp only [H]
    nlinarith
  have hMH : markedError B.sampleData.n * H ≤ 1 := by
    dsimp only [H]
    nlinarith
  have hbandT : bandTReciprocalSum B.sampleData.n B.sampleData.W ≤ K := by
    simpa only [K] using hbandTAt
  let gamma := B.canonicalEffectiveNuisanceGamma
    I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hGamma : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ), ∀ v,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
    intro z hz v
    simpa only [gamma] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhi T hbaseline hBWlarge z hz v
  have hgammaCompare : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have huniform := B.uniform_vectorField_markedRow_on_effectiveBall_of_profiles
    Delta a hgammaFull hgamma
      (mul_pos hgammaSlow (sq_pos_of_pos B.w_pos))
      (mul_nonneg B.w_pos.le hTargetScale) hCinvOrd hCreg
      hFull hGamma e
      (by intro z hz q; simpa only [gamma] using he z hz q)
      (by intro z hz; simpa only [gamma] using hvariance z hz)
      (by intro z hz; simpa only [gamma] using htarget z hz)
      hinvOrd htargetBand hH0 hK (hprofile0 B.sampleData.n) hCF
      hCprod.le hCprod.le hR0 (hmarked0 B.sampleData.n) (by omega)
      hH hbandT
      (by intro z hz; simpa only [gamma] using hsharp z hz)
      hdevSup hdevL1 hdevL2
      (fun z hz ↦ (hprofiles z hz).1)
      (fun z hz ↦ (hprofiles z hz).2)
      hF hKernelProduct hKernel hactualRow hmarkedRows
      monitoredPrimes hmonitored
  have hconstant := B.vectorFieldProfilesMarkedConstant_le_scaledMajorant
    hH0 hK (hprofile0 B.sampleData.n) hprofileOneN hEH hCF hCprod.le
      hCprod.le hR0 hRRmax (hmarked0 B.sampleData.n) hmarkedOneN hMH
      hgammaFloor hgamma hgammaCompare hCinvOrd hTband hTargetScale
      hgammaSlow hCreg hBWlarge
  have hheadMajorant :=
    B.vectorFieldProfilesMarkedScaledMajorant_le_headMajorant
      (K := K) (CF := CF) (Cprod := Cprod) (CKernel := Cprod)
      (Rmax := Rmax)
      hK hgammaFloor hCinvOrd hTband hTargetScale hgammaSlow hCreg
  have hconstantHead :
      B.vectorFieldProfilesMarkedConstant H K
          (profileError B.sampleData.n) CF Cprod Cprod R
          (markedError B.sampleData.n) gamma CinvOrd Tband
            (B.w * targetScale) (gammaSlow * B.w ^ 2) Creg ≤ Crow :=
    hconstant.trans (by simpa only [Crow] using hheadMajorant)
  intro p hp z hz
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand (hmonitored p hp)).pos
  calc
    _ ≤ B.vectorFieldProfilesMarkedConstant H K
          (profileError B.sampleData.n) CF Cprod Cprod R
          (markedError B.sampleData.n) gamma CinvOrd Tband
            (B.w * targetScale) (gammaSlow * B.w ^ 2) Creg /
        (p : ℝ) := huniform p hp z hz
    _ ≤ Crow / (p : ℝ) :=
      div_le_div_of_nonneg_right
        hconstantHead hpR.le

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal001_014.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
