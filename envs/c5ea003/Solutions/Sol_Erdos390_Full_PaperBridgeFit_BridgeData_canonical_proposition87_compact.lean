-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.canonical_proposition87_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:20:30.228087+00:00
-- url     : https://prove2.me/submissions/ca1c63c5-ab91-4fec-b78e-f869ede32f11

import Definitions.Def_erdos390_remaining_analytic_propositions_001
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_main_norm_sq_le_fastSharp_add_storedSlow
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually





section
universe u_1 u_2
theorem Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := @Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base : Erdos390.RemainingAnalyticGoal003_002.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower : Erdos390.RemainingAnalyticGoal003_001.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower_compact
end
section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice : Erdos390.RemainingAnalyticGoal001_014.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact
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





end Mesh



end

end Erdos390.Full.RegularRelativeMesh

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











theorem covariance_self_nonneg (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    0 ≤ mu.covariance F F := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (F omega * F omega)) =
      ∑ omega, mu.mass omega * F omega ^ 2 by
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * F omega) *
      (∑ omega, mu.mass omega * F omega) =
        (∑ omega, mu.mass omega * F omega) ^ 2 by ring]
  rw [PatternMixture.weightedVariance_pairDifference mu.mass F mu.mass_sum]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (mul_nonneg (mu.mass_nonneg i) (mu.mass_nonneg j)) (sq_nonneg _)

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





























/-- Every integer in the guarded sample is smooth at the paper's integral
cutoff.  Guard deletion changes neither smoothness nor the head pattern. -/
theorem value_mem_smoothNumbers (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ Nat.smoothNumbers (yNat D.n + 1) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.2





end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















/-- The logarithmic smoothness scale is strictly positive on the actual
range `n > 1`; in particular all normalized logarithms below have a
nonzero denominator. -/
theorem log_y_pos : 0 < Real.log (ArithmeticModel.y B.sampleData.n) := by
  rw [Scale.log_y (Nat.zero_lt_of_lt B.n_gt_one)]
  exact mul_pos (by norm_num) (by simpa [Scale.L, L] using B.L_pos)











































/-- Reindex the subtype sum defining the medium-prime logarithmic score
back onto the actual finite prime band.  This is an exact identity, with no
prime-sum or smooth-number approximation. -/
theorem primeLogScore_eq_bandFactorization_div
    (m : B.sampleData.Sample) :
    B.primeLogScore m =
      (∑ p ∈ ArithmeticModel.primeBand
          B.sampleData.n B.sampleData.W,
        ((B.sampleData.value m).factorization p : ℝ) *
          Real.log (p : ℝ)) /
        Real.log (ArithmeticModel.y B.sampleData.n) := by
  unfold primeLogScore ArithmeticModel.tPrime ArithmeticModel.valuation
  have hattach :
      (∑ p : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        Real.log (p.1 : ℝ) /
            Real.log (ArithmeticModel.y B.sampleData.n) *
          ((B.sampleData.value m).factorization p.1 : ℝ)) =
        ∑ p ∈ ArithmeticModel.primeBand
            B.sampleData.n B.sampleData.W,
          Real.log (p : ℝ) /
              Real.log (ArithmeticModel.y B.sampleData.n) *
            ((B.sampleData.value m).factorization p : ℝ) := by
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach
        (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
        (fun p => Real.log (p : ℝ) /
            Real.log (ArithmeticModel.y B.sampleData.n) *
          ((B.sampleData.value m).factorization p : ℝ)))
  rw [hattach, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- If every prime at most `W` is recorded in each head pattern, then the
factorization logarithm of every structured sample splits exactly into its
prescribed head contribution and the actual band `W < p ≤ floor(y)`.

The hypothesis is stated for every head tag because the sample is a tagged
disjoint union.  No convergence of head patterns, no limiting mixture, and
no prime-number estimate is used here. -/
theorem log_value_eq_headLogScore_add_bandFactorization
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    Real.log (B.sampleData.value m : ℝ) =
      B.headLogScore (B.sampleData.cellOf m).1 +
        ∑ p ∈ ArithmeticModel.primeBand
            B.sampleData.n B.sampleData.W,
          ((B.sampleData.value m).factorization p : ℝ) *
            Real.log (p : ℝ) := by
  let h : Head := (B.sampleData.cellOf m).1
  let P : HeadPattern.Pattern := B.sampleData.pattern h
  let band : Finset ℕ := ArithmeticModel.primeBand
    B.sampleData.n B.sampleData.W
  let support : Finset ℕ := (B.sampleData.value m).factorization.support
  let summand : ℕ → ℝ := fun p =>
    ((B.sampleData.value m).factorization p : ℝ) * Real.log (p : ℝ)
  have hsmooth := B.sampleData.value_mem_smoothNumbers m
  have hsupport : support ⊆ P.primes ∪ band := by
    intro p hp
    have hpFactors : p ∈ (B.sampleData.value m).primeFactors := by
      simpa [support] using hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
    have hpBelow : p ∈ (ArithmeticModel.yNat B.sampleData.n + 1).primesBelow :=
      Nat.primeFactors_subset_of_mem_smoothNumbers hsmooth hpFactors
    have hpLeY : p ≤ ArithmeticModel.yNat B.sampleData.n := by
      have hpLt : p < ArithmeticModel.yNat B.sampleData.n + 1 :=
        (Nat.mem_primesBelow.mp hpBelow).1
      omega
    by_cases hpW : p ≤ B.sampleData.W
    · apply Finset.mem_union_left
      exact (hhead h p).mpr ⟨hpPrime, hpW⟩
    · apply Finset.mem_union_right
      exact ArithmeticModel.mem_primeBand.mpr
        ⟨hpPrime, Nat.lt_of_not_ge hpW, hpLeY⟩
  have hdisjoint : Disjoint P.primes band := by
    rw [Finset.disjoint_left]
    intro p hpHead hpBand
    have hpLeW : p ≤ B.sampleData.W := (hhead h p).mp hpHead |>.2
    have hpGtW : B.sampleData.W < p :=
      ArithmeticModel.cutoff_lt_of_mem_primeBand hpBand
    exact (Nat.not_lt_of_ge hpLeW) hpGtW
  have hextend :
      ∑ p ∈ support, summand p =
        ∑ p ∈ P.primes ∪ band, summand p := by
    apply Finset.sum_subset hsupport
    intro p hpUnion hpNotSupport
    have hzero : (B.sampleData.value m).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [support] using hpNotSupport)
    simp [summand, hzero]
  have hheadSum :
      ∑ p ∈ P.primes, summand p = B.headLogScore h := by
    unfold headLogScore
    apply Finset.sum_congr (by rfl)
    intro p hp
    have hmatch := B.sampleData.value_matches_head m
    simp only [summand]
    rw [show (B.sampleData.value m).factorization p = P.exponent p by
      exact hmatch p (by simpa [P, h] using hp)]
  calc
    Real.log (B.sampleData.value m : ℝ) =
        (B.sampleData.value m).factorization.sum
          (fun p t => (t : ℝ) * Real.log (p : ℝ)) :=
      Real.log_nat_eq_sum_factorization (B.sampleData.value m)
    _ = ∑ p ∈ support, summand p := by
      rfl
    _ = ∑ p ∈ P.primes ∪ band, summand p := hextend
    _ = (∑ p ∈ P.primes, summand p) +
        ∑ p ∈ band, summand p := Finset.sum_union hdisjoint
    _ = B.headLogScore h + ∑ p ∈ band, summand p := by rw [hheadSum]
    _ = B.headLogScore (B.sampleData.cellOf m).1 +
        ∑ p ∈ ArithmeticModel.primeBand
            B.sampleData.n B.sampleData.W,
          ((B.sampleData.value m).factorization p : ℝ) *
            Real.log (p : ℝ) := by
      rfl

















/-! ### Exact main/nuisance coordinate splitting -/











































theorem combine_norm_sq (u : B.MainSpace) (z : B.NuisanceSpace) :
    ‖B.combine u z‖ ^ 2 = ‖u‖ ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs]
  change (∑ c : B.Coord, |B.combine u z c| ^ 2) =
    (∑ c : MainCoord B.GaugeIndex, |u c| ^ 2) +
      ∑ c : NuisanceCoord B.HeadIndex, |z c| ^ 2
  rw [B.sum_coord_split]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  · apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp

theorem norm_mainEmbed (u : B.MainSpace) :
    ‖B.mainEmbed u‖ = ‖u‖ := by
  have hcombine : B.combine u 0 = B.mainEmbed u := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [combine]
  have h := B.combine_norm_sq u 0
  rw [hcombine] at h
  norm_num at h
  nlinarith [norm_nonneg (B.mainEmbed u), norm_nonneg u]

theorem norm_nuisanceEmbed (z : B.NuisanceSpace) :
    ‖B.nuisanceEmbed z‖ = ‖z‖ := by
  have hcombine : B.combine 0 z = B.nuisanceEmbed z := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [combine]
  have h := B.combine_norm_sq 0 z
  rw [hcombine] at h
  norm_num at h
  nlinarith [norm_nonneg (B.nuisanceEmbed z), norm_nonneg z]

theorem mainEmbeddingCLM_norm_le_one :
    ‖B.mainEmbeddingCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖B.mainEmbed u‖ ≤ 1 * ‖u‖
  rw [B.norm_mainEmbed, one_mul]

theorem nuisanceEmbeddingCLM_norm_le_one :
    ‖B.nuisanceEmbeddingCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖B.nuisanceEmbed z‖ ≤ 1 * ‖z‖
  rw [B.norm_nuisanceEmbed, one_mul]

















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

theorem covarianceOperator_symmetric [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      inner ℝ y (B.covarianceOperator xi x) := by
  rw [B.inner_covarianceOperator, B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance FiniteProbability.covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    ring
  · ring



















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

theorem exactNuisanceRegression_isRegression [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.IsNuisanceRegression xi
      (B.exactNuisanceRegression xi hgamma hgap) := by
  intro u z
  let R := B.exactNuisanceRegression xi hgamma hgap
  have hres : B.schurResidual R u =
      B.mainEmbed u - B.nuisanceEmbed (R u) :=
    B.schurResidual_eq_sub R u
  have hcross : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.mainEmbed u)) =
      inner ℝ z (B.crossCovarianceOperator xi u) := by
    simpa only [crossCovarianceOperator, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u))).symm
  have hblock : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.nuisanceEmbed (R u))) =
      inner ℝ z (B.nuisanceCovarianceOperator xi (R u)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi
          (B.nuisanceEmbeddingCLM (R u)))).symm
  have hsecond : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.schurResidual R u)) = 0 := by
    rw [hres, map_sub, inner_sub_right, hcross, hblock]
    rw [B.exactNuisanceRegression_solve xi hgamma hgap]
    exact sub_self _
  refine ⟨?_, hsecond⟩
  rw [B.covarianceOperator_symmetric xi]
  exact hsecond

theorem exactSchurCovarianceOperator_quadratic [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
        (B.covarianceOperator xi
          (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) := by
  let R := B.exactNuisanceRegression xi hgamma hgap
  let residual := B.schurResidual R u
  have hleft : inner ℝ u
      (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ (B.mainEmbed u) (B.covarianceOperator xi residual) := by
    simpa only [exactSchurCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      B.exactSchurEmbeddingCLM_apply, R, residual] using
      (ContinuousLinearMap.adjoint_inner_right B.mainEmbeddingCLM u
        (B.covarianceOperator xi residual))
  have hres : residual = B.mainEmbed u - B.nuisanceEmbed (R u) := by
    exact B.schurResidual_eq_sub R u
  have horth :=
    (B.exactNuisanceRegression_isRegression xi hgamma hgap u (R u)).2
  have hmain : B.mainEmbed u = residual + B.nuisanceEmbed (R u) := by
    rw [hres]
    abel
  calc
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed u) (B.covarianceOperator xi residual) := hleft
    _ = inner ℝ residual (B.covarianceOperator xi residual) := by
      rw [hmain, inner_add_left, horth, add_zero]





theorem exactNuisanceRegression_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    ‖B.exactNuisanceRegression xi hgamma hgap u‖ ≤
      (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖ := by
  let r := B.exactNuisanceRegression xi hgamma hgap u
  have hcoer := hgap r
  rw [B.exactNuisanceRegression_solve xi hgamma hgap] at hcoer
  have hinner : inner ℝ r (B.crossCovarianceOperator xi u) ≤
      ‖r‖ * ‖B.crossCovarianceOperator xi u‖ :=
    real_inner_le_norm _ _
  have hcross : ‖B.crossCovarianceOperator xi u‖ ≤
      ‖B.crossCovarianceOperator xi‖ * ‖u‖ :=
    B.crossCovarianceOperator xi |>.le_opNorm u
  by_cases hr : ‖r‖ = 0
  · change ‖r‖ ≤ (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖
    rw [hr]
    exact mul_nonneg
      (div_nonneg (norm_nonneg _) (le_of_lt hgamma)) (norm_nonneg _)
  · have hrpos : 0 < ‖r‖ :=
      lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    have hcancel : gamma * ‖r‖ ≤
        ‖B.crossCovarianceOperator xi u‖ := by
      have hmul : (gamma * ‖r‖) * ‖r‖ ≤
          ‖B.crossCovarianceOperator xi u‖ * ‖r‖ := by
        calc
          (gamma * ‖r‖) * ‖r‖ = gamma * ‖r‖ ^ 2 := by ring
          _ ≤ inner ℝ r (B.crossCovarianceOperator xi u) := hcoer
          _ ≤ ‖B.crossCovarianceOperator xi u‖ * ‖r‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hrpos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    calc
      ‖B.exactNuisanceRegression xi hgamma hgap u‖ = ‖r‖ := rfl
      _ ≤ ‖B.crossCovarianceOperator xi u‖ / gamma := by
        exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)
      _ ≤ (‖B.crossCovarianceOperator xi‖ * ‖u‖) / gamma :=
        div_le_div_of_nonneg_right hcross (le_of_lt hgamma)
      _ = (‖B.crossCovarianceOperator xi‖ / gamma) * ‖u‖ := by ring

/-- Exact coordinate recombination underlying the Schur decomposition. -/
theorem combine_eq_schurResidual_add
    (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z = B.schurResidual R u + B.nuisanceEmbed (z + R u) := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c <;> simp [combine, schurResidual]

/-- With an exact regression, the full covariance quadratic form splits
into its Schur residual and the shifted nuisance quadratic form. -/
theorem covarianceForm_schur_decomposition [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (hR : B.IsNuisanceRegression xi R)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    (B.vectorFamily.tiltedMixture xi).covarianceForm (B.combine u z) =
      inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)) +
        inner ℝ (B.nuisanceEmbed (z + R u))
          (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) := by
  rw [← B.inner_covarianceOperator_self,
    B.combine_eq_schurResidual_add R u z]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [(hR u (z + R u)).1, (hR u (z + R u)).2]
  ring

/-- Explicit Euclidean loss when recombining a Schur residual with a
bounded regression. -/
theorem combine_norm_sq_le_schur_coordinates
    (R : B.MainSpace → B.NuisanceSpace) (C : ℝ)
    (hC : 0 ≤ C) (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (u : B.MainSpace) (z : B.NuisanceSpace) :
    ‖B.combine u z‖ ^ 2 ≤
      (3 + 2 * C ^ 2) * (‖u‖ ^ 2 + ‖z + R u‖ ^ 2) := by
  have hz : ‖z‖ ≤ ‖z + R u‖ + ‖R u‖ := by
    have hid : z = (z + R u) - R u := by abel
    calc
      ‖z‖ = ‖(z + R u) - R u‖ := congrArg norm hid
      _ ≤ ‖z + R u‖ + ‖R u‖ := norm_sub_le (z + R u) (R u)
  have hzC : ‖z‖ ≤ ‖z + R u‖ + C * ‖u‖ :=
    hz.trans (add_le_add (le_refl ‖z + R u‖) (hRnorm u))
  have hzsq : ‖z‖ ^ 2 ≤
      2 * ‖z + R u‖ ^ 2 + 2 * C ^ 2 * ‖u‖ ^ 2 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg z) hzC 2
    have hprod : 0 ≤ ‖z + R u‖ * (C * ‖u‖) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    calc
      ‖z‖ ^ 2 ≤ (‖z + R u‖ + C * ‖u‖) ^ 2 := hsquare
      _ ≤ 2 * ‖z + R u‖ ^ 2 + 2 * C ^ 2 * ‖u‖ ^ 2 := by
        nlinarith [sq_nonneg (‖z + R u‖ - C * ‖u‖)]
  rw [B.combine_norm_sq]
  have hcoef : 0 ≤ 3 + 2 * C ^ 2 := by positivity
  nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖z + R u‖]

/-- Concrete full-gap conclusion from the two paper Schur blocks.  In
particular the proposition-level ODE need not assume a full covariance
gap once Lemma 8.6 supplies the residual bound and the finite nuisance
block supplies its bound. -/
theorem hasCovarianceGap_of_schur [Nonempty Head]
    (xi : B.ParamSpace) (R : B.MainSpace → B.NuisanceSpace)
    (C gammaMain gammaNuisance : ℝ)
    (hC : 0 ≤ C) (hMain : 0 < gammaMain)
    (hNuisance : 0 < gammaNuisance)
    (hRnorm : ∀ u, ‖R u‖ ≤ C * ‖u‖)
    (hRegression : B.IsNuisanceRegression xi R)
    (hSchur : ∀ u,
      gammaMain * ‖u‖ ^ 2 ≤
        inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)))
    (hGamma : ∀ z,
      gammaNuisance * ‖z‖ ^ 2 ≤
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed z))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance / (3 + 2 * C ^ 2)) xi := by
  intro x
  -- Every full parameter has a unique coordinate split; define it directly.
  let u : B.MainSpace :=
    (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm (fun c =>
      match c with
      | .gauge j => x (MomentCoord.gauge j)
      | .slow => x MomentCoord.slow)
  let z : B.NuisanceSpace :=
    (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm (fun c =>
      match c with
      | .physical => x MomentCoord.physical
      | .head h => x (MomentCoord.head h))
  have hx : x = B.combine u z := by
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [u, z]
  rw [hx, B.covarianceForm_schur_decomposition xi R hRegression]
  have hminMain : min gammaMain gammaNuisance * ‖u‖ ^ 2 ≤
      inner ℝ (B.schurResidual R u)
        (B.covarianceOperator xi (B.schurResidual R u)) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖u‖)).trans
      (hSchur u)
  have hminNuisance : min gammaMain gammaNuisance * ‖z + R u‖ ^ 2 ≤
      inner ℝ (B.nuisanceEmbed (z + R u))
        (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sq_nonneg ‖z + R u‖)).trans (hGamma (z + R u))
  have hsum : min gammaMain gammaNuisance *
      (‖u‖ ^ 2 + ‖z + R u‖ ^ 2) ≤
      inner ℝ (B.schurResidual R u)
          (B.covarianceOperator xi (B.schurResidual R u)) +
        inner ℝ (B.nuisanceEmbed (z + R u))
          (B.covarianceOperator xi (B.nuisanceEmbed (z + R u))) := by
    nlinarith
  have hden : 0 < 3 + 2 * C ^ 2 := by positivity
  have hmin : 0 < min gammaMain gammaNuisance :=
    lt_min hMain hNuisance
  have hnorm := B.combine_norm_sq_le_schur_coordinates R C hC hRnorm u z
  apply le_trans ?_ hsum
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt hmin)
  nlinarith



/-! ## Exact target and moment correspondence -/



































theorem headFunctionScore_decomposition (phi : Head → ℝ)
    (m : B.sampleData.Sample) :
    B.headFunctionScore phi m = phi B.referenceHead +
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m := by
  let tag := (B.sampleData.cellOf m).1
  by_cases htag : tag = B.referenceHead
  · have hvalue : B.headFunctionScore phi m = phi B.referenceHead := by
      change phi tag = phi B.referenceHead
      rw [htag]
    rw [hvalue]
    suffices (∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) = 0 by
      rw [this, add_zero]
    apply Finset.sum_eq_zero
    intro h hh
    have hne : tag ≠ h.1 := by
      intro heq
      exact h.2 (heq.symm.trans htag)
    change (phi h.1 - phi B.referenceHead) *
      (if tag = h.1 then 1 else 0) = 0
    rw [if_neg hne, mul_zero]
  · let htagIndex : B.HeadIndex := ⟨tag, htag⟩
    change phi tag = phi B.referenceHead +
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m
    have hsum : (∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) =
        phi tag - phi B.referenceHead := by
      rw [Finset.sum_eq_single htagIndex]
      · change (phi tag - phi B.referenceHead) *
          (if tag = tag then 1 else 0) = phi tag - phi B.referenceHead
        simp
      · intro h hh hne
        have hval : h.1 ≠ tag := by
          intro heq
          exact hne (Subtype.ext heq)
        change (phi h.1 - phi B.referenceHead) *
          (if tag = h.1 then 1 else 0) = 0
        rw [if_neg hval.symm, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ htagIndex)).elim
    rw [hsum]
    ring





/-- The abstract compatibility interface is discharged by the exact
arithmetic condition used in the paper: every prime at most `W` occurs in
the head pattern, while every remaining prime factor of a structured smooth
sample lies in the actual band `W < p ≤ floor(y)`.

This theorem closes a previously explicit finite-algebra interface.  It does
not address the analytic existence or asymptotic size of the structured
cells. -/
theorem hasPrimeLogCompatibility_of_exactHeadPrimes
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W) :
    B.HasPrimeLogCompatibility := by
  let logY : ℝ := Real.log (ArithmeticModel.y B.sampleData.n)
  refine ⟨1 / logY,
    fun h => (Real.log (B.sampleData.n : ℝ) - B.headLogScore h) / logY,
    ?_⟩
  intro m
  have hsplit := B.log_value_eq_headLogScore_add_bandFactorization hhead m
  have hband :
      (∑ p ∈ ArithmeticModel.primeBand
          B.sampleData.n B.sampleData.W,
        ((B.sampleData.value m).factorization p : ℝ) *
          Real.log (p : ℝ)) =
        Real.log (B.sampleData.value m : ℝ) -
          B.headLogScore (B.sampleData.cellOf m).1 := by
    linarith
  have hvalue : (B.sampleData.value m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (B.sampleData.value_pos m))
  have hn : (B.sampleData.n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one))
  have hlogY : logY ≠ 0 := by
    exact ne_of_gt (by simpa [logY] using B.log_y_pos)
  rw [B.primeLogScore_eq_bandFactorization_div m, hband]
  unfold physicalScore headFunctionScore
  rw [Real.log_div hvalue hn]
  dsimp only [logY]
  field_simp
  ring



































theorem normalizedTarget_slow_apply [Nonempty Head]
    (Delta : Band → ℝ) :
    B.normalizedTarget Delta (MomentCoord.slow : B.Coord) =
      (B.L / B.q) *
        ((∑ j, B.bandCenter j * Delta j) / B.w) := by
  rfl

/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





theorem statistic_distance_le_diameter [Nonempty Head]
    (i j : B.sampleData.Sample) :
    ‖B.statistic i - B.statistic j‖ ≤ B.statisticDiameter := by
  calc
    ‖B.statistic i - B.statistic j‖
        ≤ ∑ k : B.sampleData.Sample, ‖B.statistic i - B.statistic k‖ := by
          exact Finset.single_le_sum
            (fun k _ => norm_nonneg (B.statistic i - B.statistic k))
            (Finset.mem_univ j)
    _ ≤ ∑ h : B.sampleData.Sample, ∑ k : B.sampleData.Sample,
          ‖B.statistic h - B.statistic k‖ := by
          exact Finset.single_le_sum
            (fun h _ => Finset.sum_nonneg fun k _ =>
              norm_nonneg (B.statistic h - B.statistic k))
            (Finset.mem_univ i)

/-- The bilinear pair-difference formula for a finite probability law.  We
record it here because it gives a completely explicit, tilt-independent
operator-norm bound for every covariance block used in Proposition 8.7. -/
theorem finiteProbability_covariance_pairDifference
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        mu.mass i * mu.mass j * (F i - F j) * (G i - G j) := by
  have hA : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F i * G i)) =
      ∑ i, mu.mass i * (F i * G i) := by
    calc
      (∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G i)) =
          ∑ i, (mu.mass i * (F i * G i)) * ∑ j, mu.mass j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ i, mu.mass i * (F i * G i) := by
        rw [mu.mass_sum]
        simp
  have hB : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F j * G j)) =
      ∑ j, mu.mass j * (F j * G j) := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, mu.mass i * mu.mass j * (F j * G j)) =
          ∑ j, (mu.mass j * (F j * G j)) * ∑ i, mu.mass i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ j, mu.mass j * (F j * G j) := by
        rw [mu.mass_sum]
        simp
  have hC : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F i * G j)) =
      (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD : (∑ i, ∑ j,
      mu.mass i * mu.mass j * (F j * G i)) =
      (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [FiniteProbability.covariance, FiniteProbability.expect]
  calc
    (∑ i, mu.mass i * (F i * G i)) -
        (∑ i, mu.mass i * F i) * (∑ i, mu.mass i * G i) =
      (1 / 2 : ℝ) *
        ((∑ i, mu.mass i * (F i * G i)) +
          (∑ j, mu.mass j * (F j * G j)) -
          (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j) -
          (∑ i, mu.mass i * F i) * (∑ j, mu.mass j * G j)) := by ring
    _ = (1 / 2 : ℝ) *
        ((∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G i)) +
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F j * G j)) -
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F i * G j)) -
          (∑ i, ∑ j, mu.mass i * mu.mass j * (F j * G i))) := by
      rw [hA, hB, hC, hD]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
        mu.mass i * mu.mass j * (F i - F j) * (G i - G j) := by
      congr 1
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring



theorem covarianceOperator_eq_covariancePairOperator [Nonempty Head]
    (xi : B.ParamSpace) :
    B.covarianceOperator xi = B.covariancePairOperator xi := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance
  rw [finiteProbability_covariance_pairDifference]
  simp only [FiniteExponentialFamily.tiltedProbability]
  unfold covariancePairOperator VectorExponentialFamily.probabilityMass
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  congr 1
  simp_rw [ContinuousLinearMap.sum_apply, inner_sum]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right,
    InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_sub_left, inner_sub_right,
    real_inner_comm (B.statistic i) y,
    real_inner_comm (B.statistic j) y]
  ring



theorem canonicalCrossBound_nonneg [Nonempty Head] :
    0 ≤ B.canonicalCrossBound := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

theorem covarianceOperator_norm_le_canonicalCrossBound [Nonempty Head]
    (xi : B.ParamSpace) :
    ‖B.covarianceOperator xi‖ ≤ B.canonicalCrossBound := by
  rw [B.covarianceOperator_eq_covariancePairOperator]
  unfold covariancePairOperator canonicalCrossBound
  calc
    ‖(1 / 2 : ℝ) • ∑ i : B.sampleData.Sample,
        ∑ j : B.sampleData.Sample,
          (B.vectorFamily.probabilityMass xi i *
            B.vectorFamily.probabilityMass xi j) •
              InnerProductSpace.rankOne ℝ
                (B.statistic i - B.statistic j)
                (B.statistic i - B.statistic j)‖
        ≤ (1 / 2 : ℝ) * ∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                ‖B.statistic i - B.statistic j‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc
            ‖∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  (B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) •
                      InnerProductSpace.rankOne ℝ
                        (B.statistic i - B.statistic j)
                        (B.statistic i - B.statistic j)‖
                ≤ ∑ i : B.sampleData.Sample,
                    ‖∑ j : B.sampleData.Sample,
                      (B.vectorFamily.probabilityMass xi i *
                        B.vectorFamily.probabilityMass xi j) •
                          InnerProductSpace.rankOne ℝ
                            (B.statistic i - B.statistic j)
                            (B.statistic i - B.statistic j)‖ :=
                  norm_sum_le _ _
            _ ≤ ∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  ‖(B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) •
                      InnerProductSpace.rankOne ℝ
                        (B.statistic i - B.statistic j)
                        (B.statistic i - B.statistic j)‖ := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact norm_sum_le _ _
            _ = ∑ i : B.sampleData.Sample,
                ∑ j : B.sampleData.Sample,
                  (B.vectorFamily.probabilityMass xi i *
                    B.vectorFamily.probabilityMass xi j) *
                    ‖B.statistic i - B.statistic j‖ ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro i _
                  apply Finset.sum_congr rfl
                  intro j _
                  have hi : 0 ≤ B.vectorFamily.probabilityMass xi i :=
                    B.vectorFamily.scalarFamily.probabilityMass_nonneg xi i
                  have hj : 0 ≤ B.vectorFamily.probabilityMass xi j :=
                    B.vectorFamily.scalarFamily.probabilityMass_nonneg xi j
                  rw [norm_smul, InnerProductSpace.norm_rankOne,
                    Real.norm_eq_abs,
                    abs_of_nonneg (mul_nonneg hi hj)]
                  ring
    _ ≤ (1 / 2 : ℝ) * ∑ i : B.sampleData.Sample,
          ∑ j : B.sampleData.Sample,
            (B.vectorFamily.probabilityMass xi i *
              B.vectorFamily.probabilityMass xi j) *
              B.statisticDiameter ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _)
            (B.statistic_distance_le_diameter i j) 2)
          (mul_nonneg
            (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi i)
            (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi j))
    _ = B.statisticDiameter ^ 2 / 2 := by
      have hsum : ∑ i : B.sampleData.Sample,
          B.vectorFamily.probabilityMass xi i = 1 :=
        B.vectorFamily.scalarFamily.probabilityMass_sum xi
      have hdouble :
          (∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                B.statisticDiameter ^ 2) =
              B.statisticDiameter ^ 2 := by
        calc
        (∑ i : B.sampleData.Sample,
            ∑ j : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.vectorFamily.probabilityMass xi j) *
                B.statisticDiameter ^ 2) =
            ∑ i : B.sampleData.Sample,
              (B.vectorFamily.probabilityMass xi i *
                B.statisticDiameter ^ 2) *
                ∑ j : B.sampleData.Sample,
                  B.vectorFamily.probabilityMass xi j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ∑ i : B.sampleData.Sample,
              B.vectorFamily.probabilityMass xi i *
                B.statisticDiameter ^ 2 := by rw [hsum]; simp
        _ = (∑ i : B.sampleData.Sample,
              B.vectorFamily.probabilityMass xi i) *
                B.statisticDiameter ^ 2 := by rw [Finset.sum_mul]
        _ = B.statisticDiameter ^ 2 := by rw [hsum, one_mul]
      rw [hdouble]
      ring

/-- In particular, the main-to-nuisance cross block has the same canonical
tilt-independent bound.  Thus Proposition 8.7 does not need an additional
analytic cross-block hypothesis or a box-dependent constant. -/
theorem crossCovarianceOperator_norm_le_canonicalCrossBound
    [Nonempty Head] (xi : B.ParamSpace) :
    ‖B.crossCovarianceOperator xi‖ ≤ B.canonicalCrossBound := by
  have hAdj : ‖B.nuisanceEmbeddingCLM.adjoint‖ ≤ 1 := by
    simpa using B.nuisanceEmbeddingCLM_norm_le_one
  have hinner :
      ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ ≤
        B.canonicalCrossBound * 1 := by
    calc
      ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ ≤
          ‖B.covarianceOperator xi‖ * ‖B.mainEmbeddingCLM‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B.canonicalCrossBound * 1 :=
        mul_le_mul (B.covarianceOperator_norm_le_canonicalCrossBound xi)
          B.mainEmbeddingCLM_norm_le_one
          (norm_nonneg _) B.canonicalCrossBound_nonneg
  unfold crossCovarianceOperator
  calc
    ‖B.nuisanceEmbeddingCLM.adjoint.comp
        ((B.covarianceOperator xi).comp B.mainEmbeddingCLM)‖ ≤
        ‖B.nuisanceEmbeddingCLM.adjoint‖ *
          ‖(B.covarianceOperator xi).comp B.mainEmbeddingCLM‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (B.canonicalCrossBound * 1) :=
      mul_le_mul hAdj hinner (norm_nonneg _) zero_le_one
    _ = B.canonicalCrossBound := by ring

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









end

end Erdos390.Full.ArithmeticBandGeometry.Partition

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

/-- Bilinear form of the actual nuisance covariance block. -/
theorem inner_nuisanceCovarianceOperator_bilinear [Nonempty Head]
    (xi : B.ParamSpace) (z a : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceOperator xi a) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) := by
  have hadjoint :
      inner ℝ z (B.nuisanceCovarianceOperator xi a) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed a)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM a)))
  rw [hadjoint, B.inner_covarianceOperator]
  congr 1
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
        (B.mainStatistic m)]
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine a (B.nuisanceStatistic m)
        (B.mainStatistic m)]



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

/-- Exact Schur orthogonality of the actual nuisance residual. -/
theorem nuisanceResidualScore_covariance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.nuisanceResidualScore xi hgamma hgap F) = 0 := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  unfold nuisanceResidualScore
  rw [covariance_sub_right]
  have hfirst := B.inner_nuisanceCovarianceVector xi F z
  have hsecond := B.inner_nuisanceCovarianceOperator_bilinear xi z a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ z v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ z (B.nuisanceCovarianceOperator xi a) =
    inner ℝ z (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hfirst, hsecond] at hsolve
  exact sub_eq_zero.mpr hsolve.symm





theorem actualCompensatedScore_covariance_nuisance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualCompensatedScore xi hgamma hgap q) = 0 := by
  exact B.nuisanceResidualScore_covariance_zero xi hgamma hgap
    (B.postBandPrimeScore q) z





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





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityCovarianceCauchySchwarz -/
section


/-!
# Cauchy--Schwarz for a literal finite covariance

The two-stage Schur argument needs Cauchy--Schwarz for the actual finite
tilted law, not an abstract positive-semidefinite assumption.  This file
derives it directly from the mass function of `FiniteProbability`.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Covariance is the weighted inner product of the two centered functions. -/
theorem covariance_eq_sum_mass_mul_centered
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      ∑ omega, mu.mass omega * (F omega - mu.expect F) *
        (G omega - mu.expect G) := by
  unfold covariance
  generalize hEF : mu.expect F = EF
  generalize hEG : mu.expect G = EG
  unfold expect at hEF hEG ⊢
  symm
  calc
    (∑ omega, mu.mass omega * (F omega - EF) * (G omega - EG)) =
        (∑ omega, mu.mass omega * (F omega * G omega)) -
          (∑ omega, mu.mass omega * F omega) * EG -
          EF * (∑ omega, mu.mass omega * G omega) +
          (EF * EG) * (∑ omega, mu.mass omega) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega, mu.mass omega * (F omega * G omega)) - EF * EG := by
      rw [mu.mass_sum, ← hEF, ← hEG]
      ring

/-- Squared Cauchy--Schwarz inequality for the exact finite covariance. -/
theorem covariance_sq_le_mul_self
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G ^ 2 ≤
      mu.covariance F F * mu.covariance G G := by
  let f : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (F omega - mu.expect F)
  let g : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (G omega - mu.expect G)
  have hcross : (∑ omega, f omega * g omega) = mu.covariance F G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f, g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    calc
      Real.sqrt (mu.mass omega) * (F omega - mu.expect F) *
          (Real.sqrt (mu.mass omega) * (G omega - mu.expect G)) =
          Real.sqrt (mu.mass omega) ^ 2 *
            (F omega - mu.expect F) * (G omega - mu.expect G) := by ring
      _ = mu.mass omega * (F omega - mu.expect F) *
            (G omega - mu.expect G) := by rw [hsqrt]
  have hleft : (∑ omega, f omega ^ 2) = mu.covariance F F := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hright : (∑ omega, g omega ^ 2) = mu.covariance G G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simpa only [hcross, hleft, hright] using hCS

end

end Erdos390.Full.FiniteProbability

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









theorem projectRawBandVector_sub [Nonempty Band]
    (x y : Band → ℝ) :
    B.projectRawBandVector (x - y) =
      B.projectRawBandVector x - B.projectRawBandVector y := by
  apply Subtype.ext
  funext j
  change weightedGaugeProjection B.harmonicMass B.bandCenter (x - y) j =
    weightedGaugeProjection B.harmonicMass B.bandCenter x j -
      weightedGaugeProjection B.harmonicMass B.bandCenter y j
  have hsum :
      (∑ k : Band,
        B.harmonicMass k * B.bandCenter k * (x k - y k)) =
      (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) -
        ∑ k : Band, B.harmonicMass k * B.bandCenter k * y k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold weightedGaugeProjection
  simp only [Pi.sub_apply, hsum]
  ring

/-- The kernel of the exact arithmetic projection is orthogonal to every
raw-gauge vector in the `D` pairing. -/
theorem weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    [Nonempty Band]
    (x : Band → ℝ) (q : B.RawBandGauge)
    (hx : B.projectRawBandVector x = 0) :
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) = 0 := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hxcoord (j : Band) : x j = B.bandCenter j * mu := by
    have hzero := congrArg (fun v : B.RawBandGauge ↦ v.1 j) hx
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = 0 at hzero
    unfold weightedGaugeProjection at hzero
    dsimp only [mu]
    linarith
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) =
        mu * ∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxcoord j]
      unfold rawGaugeWeight
      ring
    _ = 0 := by
      have hq := q.2
      change (∑ j : Band,
        rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
      rw [hq, mul_zero]







theorem normalizedBandCovarianceRow_sub [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ F m - G m) =
      B.normalizedBandCovarianceRow xi F -
        B.normalizedBandCovarianceRow xi G := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.normalizedBandCovarianceRow_add,
    B.normalizedBandCovarianceRow_smul]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring













theorem nuisanceResidualScore_sub [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ F m - G m) =
      fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m -
        B.nuisanceResidualScore xi hgamma hgap G m := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.nuisanceResidualScore_add xi hgamma hgap,
    B.nuisanceResidualScore_smul xi hgamma hgap]
  funext m
  ring





theorem bandRegressionScore_sub
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q - r) =
      fun m ↦ B.bandRegressionScore q m - B.bandRegressionScore r m := by
  have hneg : -r = (-1 : ℝ) • r := (neg_one_smul ℝ r).symm
  rw [sub_eq_add_neg, B.bandRegressionScore_add, hneg,
    B.bandRegressionScore_smul]
  funext m
  ring













theorem actualBandRegression_normalEquation [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.actualBandSchurLinearMap xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e) =
      B.actualBandRegressionTarget xi hgamma hgap := by
  rw [← he]
  exact e.apply_symm_apply _

/-- The constructed first-stage regression makes the literal normalized
band row of the fully nuisance-projected score vanish after arithmetic gauge
projection. -/
theorem actualBandRegression_projectedResidual_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.actualCompensatedScore xi hgamma hgap
          (B.actualBandRegression xi hgamma hgap e))) = 0 := by
  let q := B.actualBandRegression xi hgamma hgap e
  have hnormal := B.actualBandRegression_normalEquation
    xi hgamma hgap e he
  have hpost : B.postBandPrimeScore q =
      fun m ↦ B.slowScore m - B.bandRegressionScore q m := by
    funext m
    exact B.postBandPrimeScore_eq_slow_sub_bandRegression q m
  have hresidual :
      B.actualCompensatedScore xi hgamma hgap q =
        fun m ↦
          B.nuisanceResidualScore xi hgamma hgap B.slowScore m -
          B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q) m := by
    unfold actualCompensatedScore
    rw [hpost, B.nuisanceResidualScore_sub xi hgamma hgap]
  rw [hresidual, B.normalizedBandCovarianceRow_sub,
    B.projectRawBandVector_sub]
  change B.actualBandRegressionTarget xi hgamma hgap -
      B.actualBandSchurLinearMap xi hgamma hgap q = 0
  rw [← hnormal]
  exact sub_self _

/-- Exact covariance of a raw gauge score with an arbitrary finite score,
written in the normalized band-row coordinates. -/
theorem covariance_bandRegressionScore_eq_weightedRow [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore q) F =
      ∑ j : Band, B.harmonicMass j * q.1 j *
        B.normalizedBandCovarianceRow xi F j := by
  unfold bandRegressionScore normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteProbability.covariance_smul_left]
  have hH := B.harmonicMass_pos j
  field_simp [ne_of_gt hH]

/-- The first-stage normal equation is genuine covariance orthogonality to
every arithmetic gauge score. -/
theorem actualBandRegression_covariance_gauge_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (r : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e)) = 0 := by
  rw [B.covariance_bandRegressionScore_eq_weightedRow]
  exact B.weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    (B.normalizedBandCovarianceRow xi
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e))) r
    (B.actualBandRegression_projectedResidual_zero
      xi hgamma hgap e he)

















/-- The fully fitted literal score is orthogonal both to every nuisance
score and to every raw arithmetic-gauge band score. -/
theorem actualTwoStageCompensatedScore_orthogonal
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    (∀ z : B.NuisanceSpace,
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0) ∧
    ∀ r : B.RawBandGauge,
      (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  constructor
  · intro z
    exact B.actualCompensatedScore_covariance_nuisance_zero
      xi hgamma hgap (B.actualBandRegression xi hgamma hgap e) z
  · intro r
    exact B.actualBandRegression_covariance_gauge_zero
      xi hgamma hgap e he r

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











/-- A pointwise full covariance gap obtained from the two literal Schur
blocks with a constant which is uniform in the parameter.  The nuisance
regression is the actual finite operator `Gamma_{xi,n}^{-1} B_{xi,n}`;
the only uniformization is the already proved canonical bound for the
cross-covariance operator.  Thus a proposition-level theorem can consume
the nuisance and main/slow gaps separately, without assuming the full
Jacobian gap as an additional analytic input. -/
theorem hasCovarianceGap_of_uniform_exactSchur [Nonempty Head]
    (xi : B.ParamSpace) (gammaMain gammaNuisance : ℝ)
    (hgammaMain : 0 < gammaMain)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hSchur : ∀ u, gammaMain * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance /
        (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)) xi := by
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hC : 0 ≤ B.canonicalCrossBound / gammaNuisance :=
    div_nonneg B.canonicalCrossBound_nonneg hgammaNuisance.le
  apply B.hasCovarianceGap_of_schur xi R
    (B.canonicalCrossBound / gammaNuisance)
    gammaMain gammaNuisance hC hgammaMain hgammaNuisance
  · intro u
    dsimp only [R]
    calc
      ‖B.exactNuisanceRegression xi hgammaNuisance hGamma u‖ ≤
          (‖B.crossCovarianceOperator xi‖ / gammaNuisance) * ‖u‖ :=
        B.exactNuisanceRegression_norm_le xi hgammaNuisance hGamma u
      _ ≤ (B.canonicalCrossBound / gammaNuisance) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (B.crossCovarianceOperator_norm_le_canonicalCrossBound xi)
            hgammaNuisance.le)
          (norm_nonneg u)
  · dsimp only [R]
    exact B.exactNuisanceRegression_isRegression
      xi hgammaNuisance hGamma
  · dsimp only [R]
    exact hSchur
  · intro z
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right] using hGamma z

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

/- Source module: Erdos390.Full.PaperWeightedGaugeDGeometry -/
section


/-!
# Finite `D`-pairing geometry in the paper's sharp gauge

These are the exact finite weighted inequalities used when covariance
Cauchy--Schwarz is combined with the sharp-gauge inverse.  No continuum
centre or limiting weight is introduced.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band] [Nonempty Band]





theorem rawDLowerWeight_le (H alpha : Band → ℝ) (j : Band) :
    rawDLowerWeight H alpha ≤ H j * alpha j ^ 2 := by
  classical
  unfold rawDLowerWeight
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Positivity of the literal finite minimum. -/
theorem rawDLowerWeight_pos
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0) :
    0 < rawDLowerWeight H alpha := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun j ↦ H j * alpha j ^ 2)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  have hmem := Finset.min'_mem s hs
  obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hmem
  have hAlphaSq : 0 < alpha j ^ 2 := sq_pos_of_ne_zero (hAlpha j)
  unfold rawDLowerWeight
  change 0 < s.min' hs
  rw [← hEq]
  exact mul_pos (hH j) hAlphaSq

/-- The `D` quadratic form controls the paper's sharp supremum norm by the
smallest literal sharp diagonal weight. -/
theorem rawDLowerWeight_mul_paperSharpNorm_sq_le
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q : RawGaugeSpace H alpha) :
    rawDLowerWeight H alpha *
        paperSharpNorm H alpha hAlpha q ^ 2 ≤
      rawDPairing H alpha q q := by
  classical
  let f : Band → ℝ := fun j ↦ q.1 j / alpha j
  obtain ⟨j, hj, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k : Band ↦ ‖f k‖₊)
  have hnorm : paperSharpNorm H alpha hAlpha q = |f j| := by
    rw [paperSharpNorm_eq_piNorm]
    change ‖f‖ = |f j|
    rw [Pi.norm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty, hsup]
    simp only [coe_nnnorm, Real.norm_eq_abs]
  have hmin0 : 0 ≤ rawDLowerWeight H alpha :=
    (rawDLowerWeight_pos H alpha hH hAlpha).le
  have hterm :
      rawDLowerWeight H alpha * |f j| ^ 2 ≤ H j * q.1 j ^ 2 := by
    calc
      rawDLowerWeight H alpha * |f j| ^ 2 ≤
          (H j * alpha j ^ 2) * |f j| ^ 2 :=
        mul_le_mul_of_nonneg_right (rawDLowerWeight_le H alpha j)
          (sq_nonneg _)
      _ = H j * q.1 j ^ 2 := by
        dsimp only [f]
        rw [sq_abs]
        field_simp [hAlpha j]
  rw [hnorm]
  exact hterm.trans (by
    unfold rawDPairing
    simpa only [pow_two, mul_assoc] using
      (Finset.single_le_sum
        (fun k hk ↦ mul_nonneg (hH k).le (sq_nonneg (q.1 k)))
        (Finset.mem_univ j)))

/-- Absolute `D` pairing is bounded by the total sharp weight times the two
paper-sharp norms. -/
theorem abs_rawDPairing_le_sharpWeightTotal_mul
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q r : RawGaugeSpace H alpha) :
    |rawDPairing H alpha q r| ≤
      sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
        paperSharpNorm H alpha hAlpha r := by
  have hq (j : Band) :
      |q.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha q := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ q.1 k / alpha k)).mp le_rfl j)
  have hr (j : Band) :
      |r.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha r := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ r.1 k / alpha k)).mp le_rfl j)
  have hq0 : 0 ≤ paperSharpNorm H alpha hAlpha q := norm_nonneg _
  have hr0 : 0 ≤ paperSharpNorm H alpha hAlpha r := norm_nonneg _
  calc
    |rawDPairing H alpha q r| ≤
        ∑ j, |H j * q.1 j * r.1 j| := by
      unfold rawDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (H j * alpha j ^ 2) *
          paperSharpNorm H alpha hAlpha q *
            paperSharpNorm H alpha hAlpha r := by
      apply Finset.sum_le_sum
      intro j hj
      have hweight : 0 ≤ H j * alpha j ^ 2 :=
        mul_nonneg (hH j).le (sq_nonneg _)
      have hratio :
          |q.1 j / alpha j| * |r.1 j / alpha j| ≤
            paperSharpNorm H alpha hAlpha q *
              paperSharpNorm H alpha hAlpha r :=
        mul_le_mul (hq j) (hr j) (abs_nonneg _) hq0
      calc
        |H j * q.1 j * r.1 j| =
            (H j * alpha j ^ 2) *
              (|q.1 j / alpha j| * |r.1 j / alpha j|) := by
          rw [abs_mul, abs_mul, abs_of_pos (hH j), abs_div, abs_div,
            ← sq_abs]
          field_simp [abs_ne_zero.mpr (hAlpha j)]
        _ ≤ (H j * alpha j ^ 2) *
              (paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r) :=
          mul_le_mul_of_nonneg_left hratio hweight
        _ = (H j * alpha j ^ 2) *
              paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r := by ring
    _ = sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
          paperSharpNorm H alpha hAlpha r := by
      unfold sharpWeightTotal sharpWeight
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.PaperExactSchurTwoStageQuadratic -/
section


/-!
# Exact quadratic attachment for the two-stage Schur regression

This file supplies the finite-dimensional algebra between the arithmetic
band inverse of Lemma 8.4 and the compensated slow score of Lemma 8.6.  In
particular, no limiting operator, mesh estimate, or covariance lower bound
is assumed here.

The first identity identifies the quadratic form of the literal projected
band Schur operator with the variance of the nuisance-residual band score.
The second identity proves that the fast band residual and the fitted slow
score are exactly covariance-orthogonal.  Combining them gives the exact
fast/slow quadratic decomposition of the main Schur block used in
Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Projecting a normalized band row does not change its pairing with an
arithmetic-gauge vector.  This is the exact finite arithmetic centering
identity; in particular it does not replace the arithmetic centres by
continuum cell centres. -/
theorem weighted_pairing_projectRawBandVector
    [Nonempty Band]
    (q : B.RawBandGauge) (x : Band → ℝ) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.projectRawBandVector x).1 j) =
      ∑ j : Band, B.harmonicMass j * q.1 j * x j := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hcoord (j : Band) :
      (B.projectRawBandVector x).1 j = x j - B.bandCenter j * mu := by
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = _
    unfold weightedGaugeProjection
    rfl
  rw [show (∑ j : Band, B.harmonicMass j * q.1 j *
      (B.projectRawBandVector x).1 j) =
      (∑ j : Band, B.harmonicMass j * q.1 j * x j) -
        mu * (∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoord]
    unfold rawGaugeWeight
    ring]
  have hq := q.2
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
  rw [hq, mul_zero, sub_zero]

/-- The quadratic form of the literal arithmetic band Schur map is exactly
the variance of the band score after the actual finite nuisance regression.
This is an equality at finite `n`, in the arithmetic `D`-pairing. -/
theorem actualBandSchur_quadratic_eq_residualVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  let F : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  let R : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap F
  have hF : F = fun m ↦ R m + Z m := by
    funext m
    simp only [F, R, Z, a]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Z R = 0 := by
    simpa only [Z, R, a] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap F a
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi R j := by
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi R)
    _ = (B.tiltedLaw xi).covariance F R := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q R).symm
    _ = (B.tiltedLaw xi).covariance R R := by
      rw [hF, FiniteProbability.covariance_add_left, horth, add_zero]

/-- Bilinear form of the preceding identity.  It is needed for the
covariance Cauchy--Schwarz conversion from a sharp inverse bound to a
positive `D`-quadratic gap. -/
theorem actualBandSchur_bilinear_eq_residualCovariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q r : B.RawBandGauge) :
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore r)) := by
  let Fq : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let Fr : B.sampleData.Sample → ℝ := B.bandRegressionScore r
  let aq : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap Fq
  let Zq : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ aq (B.nuisanceStatistic m)
  let Rq : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fq
  let Rr : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fr
  have hFq : Fq = fun m ↦ Rq m + Zq m := by
    funext m
    simp only [Fq, Rq, Zq, aq]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Zq Rr = 0 := by
    simpa only [Zq, Rr, aq] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap Fr aq
  calc
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi Rr j := by
      unfold bandDPairing
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi Rr)
    _ = (B.tiltedLaw xi).covariance Fq Rr := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q Rr).symm
    _ = (B.tiltedLaw xi).covariance Rq Rr := by
      rw [hFq, FiniteProbability.covariance_add_left, horth, add_zero]

/-- Covariance Cauchy--Schwarz converts an inverse bound for the literal
band Schur map into a quantitative `D`-quadratic estimate.  The two displayed
`D` comparisons are pure finite weighted-gauge geometry; they are kept as
arguments here so this analytic attachment cannot silently change norms. -/
theorem actualBandSchur_quadratic_mul_bound_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 ≤ Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 ≤ Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    Dlower ^ 2 *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (Dupper * Cinv) *
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q)) := by
  let S : B.RawBandGauge → ℝ := fun v ↦
    paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) v
  let R : B.RawBandGauge → B.sampleData.Sample → ℝ := fun v ↦
    B.nuisanceResidualScore xi hgamma hgap (B.bandRegressionScore v)
  let Q : B.RawBandGauge → ℝ := fun v ↦
    (B.tiltedLaw xi).covariance (R v) (R v)
  let y : B.RawBandGauge := e.symm q
  have hey : B.actualBandSchurLinearMap xi hgamma hgap y = q := by
    rw [← he, LinearEquiv.apply_symm_apply]
  have hDqq : Dlower * S q ^ 2 ≤ B.bandDPairing q q := hDdiag q
  have hDqq0 : 0 ≤ B.bandDPairing q q :=
    (mul_nonneg hDlower (sq_nonneg _)).trans hDqq
  have hcross : B.bandDPairing q q =
      (B.tiltedLaw xi).covariance (R q) (R y) := by
    calc
      B.bandDPairing q q =
          B.bandDPairing q
            (B.actualBandSchurLinearMap xi hgamma hgap y) := by rw [hey]
      _ = (B.tiltedLaw xi).covariance (R q) (R y) :=
        B.actualBandSchur_bilinear_eq_residualCovariance
          xi hgamma hgap q y
  have hcs : (B.bandDPairing q q) ^ 2 ≤ Q q * Q y := by
    rw [hcross]
    exact (B.tiltedLaw xi).covariance_sq_le_mul_self (R q) (R y)
  have hQy : Q y = B.bandDPairing y q := by
    calc
      Q y = B.bandDPairing y
          (B.actualBandSchurLinearMap xi hgamma hgap y) :=
        (B.actualBandSchur_quadratic_eq_residualVariance
          xi hgamma hgap y).symm
      _ = B.bandDPairing y q := by rw [hey]
  have hSy : S y ≤ Cinv * S q := hinv q
  have hS0 (v : B.RawBandGauge) : 0 ≤ S v := by
    exact norm_nonneg _
  have hQy0 : 0 ≤ Q y :=
    (B.tiltedLaw xi).covariance_self_nonneg (R y)
  have hQq0 : 0 ≤ Q q :=
    (B.tiltedLaw xi).covariance_self_nonneg (R q)
  have hQyUpper : Q y ≤ Dupper * Cinv * S q ^ 2 := by
    rw [hQy]
    calc
      B.bandDPairing y q ≤ |B.bandDPairing y q| := le_abs_self _
      _ ≤ Dupper * S y * S q := hDbilin y q
      _ ≤ Dupper * (Cinv * S q) * S q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSy hDupper) (hS0 q)
      _ = Dupper * Cinv * S q ^ 2 := by ring
  by_cases hSq : S q = 0
  · change Dlower ^ 2 * S q ^ 2 ≤ (Dupper * Cinv) * Q q
    rw [hSq]
    norm_num
    exact mul_nonneg (mul_nonneg hDupper hCinv) hQq0
  · have hSqPos : 0 < S q := lt_of_le_of_ne (hS0 q) (Ne.symm hSq)
    have hDsq : (Dlower * S q ^ 2) ^ 2 ≤
        (B.bandDPairing q q) ^ 2 := by
      exact sq_le_sq₀ (mul_nonneg hDlower (sq_nonneg _)) hDqq0 |>.2 hDqq
    have hmaster : (Dlower * S q ^ 2) ^ 2 ≤
        Q q * (Dupper * Cinv * S q ^ 2) := by
      exact hDsq.trans (hcs.trans
        (mul_le_mul_of_nonneg_left hQyUpper hQq0))
    nlinarith [sq_pos_of_pos hSqPos]

/-- Division form of the preceding quantitative gap. -/
theorem actualBandSchur_quadratic_lower_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 < Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 < Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    (Dlower ^ 2 / (Dupper * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  have hmul := B.actualBandSchur_quadratic_mul_bound_of_inverse
    xi hgamma hgap e he hCinv.le hDlower hDupper.le
    hinv hDdiag hDbilin q
  have hden : 0 < Dupper * Cinv := mul_pos hDupper hCinv
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Literal arithmetic specialization of the inverse-to-quadratic theorem.
The two `D` constants and both weighted inequalities are now conclusions of
the finite positive harmonic masses and centres. -/
theorem actualBandSchur_quadratic_lower_of_inverse_arithmetic
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ} (hCinv : 0 < Cinv)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (q : B.RawBandGauge) :
    (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
        (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  apply B.actualBandSchur_quadratic_lower_of_inverse
    xi hgamma hgap e he hCinv
    (rawDLowerWeight_pos B.harmonicMass B.bandCenter
      B.harmonicMass_pos
      (B.partition.center_ne_zero B.n_gt_one)).le
    B.sharpBandWeightTotal_pos
    hinv
  · intro v
    simpa only [bandDPairing, rawDPairing] using
      rawDLowerWeight_mul_paperSharpNorm_sq_le
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v
  · intro v u
    simpa only [bandDPairing, rawDPairing] using
      abs_rawDPairing_le_sharpWeightTotal_mul
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v u

/-- The nuisance-residual fast band score is exactly orthogonal to the
two-stage compensated slow score.  Both the band normal equation and the
nuisance normal equation are used; neither orthogonality is postulated. -/
theorem fastResidual_covariance_twoStageCompensated_eq_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  let a : B.NuisanceSpace := B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  have hband : (B.tiltedLaw xi).covariance
      (B.bandRegressionScore qFast)
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).2 qFast
  have hnuisance : (B.tiltedLaw xi).covariance
      (fun m ↦ inner ℝ a (B.nuisanceStatistic m))
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).1 a
  have hresidual :
      B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast) =
        fun m ↦ B.bandRegressionScore qFast m -
          inner ℝ a (B.nuisanceStatistic m) := by
    rfl
  rw [hresidual]
  have hsub : (fun m ↦ B.bandRegressionScore qFast m -
      inner ℝ a (B.nuisanceStatistic m)) =
      fun m ↦ B.bandRegressionScore qFast m +
        (-1 : ℝ) * inner ℝ a (B.nuisanceStatistic m) := by
    funext m
    ring
  rw [hsub, FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_smul_left, hband, hnuisance]
  ring

/-- Exact Pythagorean identity for the finite two-stage regression. -/
theorem covariance_fast_add_slow_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) (lambda : ℝ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦
          B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast) m +
            lambda * B.actualTwoStageCompensatedScore
              xi hgamma hgap e m)
        (fun m ↦
          B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast) m +
            lambda * B.actualTwoStageCompensatedScore
              xi hgamma hgap e m) =
      (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) +
        lambda ^ 2 * (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.actualTwoStageCompensatedScore xi hgamma hgap e) := by
  let F := B.nuisanceResidualScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  let C := B.actualTwoStageCompensatedScore xi hgamma hgap e
  have hFC : (B.tiltedLaw xi).covariance F C = 0 := by
    exact B.fastResidual_covariance_twoStageCompensated_eq_zero
      xi hgamma hgap e he qFast
  have hCF : (B.tiltedLaw xi).covariance C F = 0 := by
    rw [(B.tiltedLaw xi).covariance_comm]
    exact hFC
  rw [FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_smul_left,
    FiniteProbability.covariance_smul_right,
    FiniteProbability.covariance_smul_right,
    hFC, hCF]
  rw [FiniteProbability.covariance_smul_left]
  ring

/-- Exact quadratic decomposition of the actual main Schur block.  For the
canonical first-stage regression `qReg`, every main vector is written with
raw coordinate `qFast - lambda qReg` and stored slow coordinate
`w * lambda`.  The resulting Schur quadratic form is the sum of the fast
band residual variance and `lambda^2` times the fully compensated slow
variance. -/
theorem exactSchur_quadratic_eq_fast_add_slow_twoStage
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (u : B.MainSpace) (qFast : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda •
      B.actualBandRegression xi hgamma hgap e)
    (hslow : u MainCoord.slow = B.w * lambda) :
    inner ℝ u (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast)) +
        lambda ^ 2 * (B.tiltedLaw xi).covariance
          (B.actualTwoStageCompensatedScore xi hgamma hgap e)
          (B.actualTwoStageCompensatedScore xi hgamma hgap e) := by
  rw [B.exactSchurCovarianceOperator_quadratic,
    B.inner_covarianceOperator]
  have hscore := B.vectorScore_exactSchurResidual_fast_add_compensated
    xi hgamma hgap u qFast
      (B.actualBandRegression xi hgamma hgap e) lambda hq hslow
  have hinnerScore :
      (fun m ↦ inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)
        (B.statistic m)) =
      fun m ↦ B.vectorFamily.scalarFamily.score m
        (B.schurResidual
          (B.exactNuisanceRegression xi hgamma hgap) u) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hinnerScore, hscore]
  exact B.covariance_fast_add_slow_twoStage
    xi hgamma hgap e he qFast lambda

/-- Deterministic fast/slow coercivity assembly.  The only coordinate input
is the displayed comparison between the concrete Euclidean `MainSpace` norm
and the intrinsic sharp-fast/stored-slow coordinates.  The analytic inputs
are exactly the fast band variance lower bound and the compensated slow
variance lower bound; an undischarged Schur-gap hypothesis is not used. -/
theorem exactSchurGap_of_fastSlow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Ccoord : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCcoord : 0 < Ccoord)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hcoordinate : ∀ (u : B.MainSpace) (qFast : B.RawBandGauge)
        (lambda : ℝ),
      B.rawGaugeOfMain u = qFast - lambda •
          B.actualBandRegression xi hgammaNuisance hGamma e →
      u MainCoord.slow = B.w * lambda →
      ‖u‖ ^ 2 ≤ Ccoord *
        (paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 +
          (B.w * lambda) ^ 2)) :
    ∀ u,
      (min gammaFast gammaSlow / Ccoord) * ‖u‖ ^ 2 ≤
        inner ℝ
          (B.schurResidual
            (B.exactNuisanceRegression
              xi hgammaNuisance hGamma) u)
          (B.covarianceOperator xi
            (B.schurResidual
              (B.exactNuisanceRegression
                xi hgammaNuisance hGamma) u)) := by
  intro u
  let lambda : ℝ := u MainCoord.slow / B.w
  let qReg : B.RawBandGauge :=
    B.actualBandRegression xi hgammaNuisance hGamma e
  let qFast : B.RawBandGauge := B.rawGaugeOfMain u + lambda • qReg
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simp only [qFast]
    abel
  have hstored : u MainCoord.slow = B.w * lambda := by
    dsimp only [lambda]
    field_simp [ne_of_gt B.w_pos]
  have hcoord := hcoordinate u qFast lambda hq (by
    simpa only [qReg] using hstored)
  have hdecomp := B.exactSchur_quadratic_eq_fast_add_slow_twoStage
    xi hgammaNuisance hGamma e he u qFast lambda hq
      (by simpa only [qReg] using hstored)
  let S : ℝ := paperSharpNorm B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) qFast
  let Vfast : ℝ := (B.tiltedLaw xi).covariance
    (B.nuisanceResidualScore xi hgammaNuisance hGamma
      (B.bandRegressionScore qFast))
    (B.nuisanceResidualScore xi hgammaNuisance hGamma
      (B.bandRegressionScore qFast))
  let Vslow : ℝ := (B.tiltedLaw xi).covariance
    (B.actualTwoStageCompensatedScore xi hgammaNuisance hGamma e)
    (B.actualTwoStageCompensatedScore xi hgammaNuisance hGamma e)
  have hfast' : gammaFast * S ^ 2 ≤ Vfast := hfast qFast
  have hslow' : gammaSlow * B.w ^ 2 ≤ Vslow := hslow
  have hlambdaSq : 0 ≤ lambda ^ 2 := sq_nonneg _
  have hslowScaled : gammaSlow * (B.w * lambda) ^ 2 ≤
      lambda ^ 2 * Vslow := by
    have := mul_le_mul_of_nonneg_left hslow' hlambdaSq
    nlinarith
  have hminFast : min gammaFast gammaSlow * S ^ 2 ≤ Vfast :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg S)).trans
      hfast'
  have hminSlow : min gammaFast gammaSlow * (B.w * lambda) ^ 2 ≤
      lambda ^ 2 * Vslow :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (sq_nonneg (B.w * lambda))).trans hslowScaled
  have hsum : min gammaFast gammaSlow *
      (S ^ 2 + (B.w * lambda) ^ 2) ≤
      Vfast + lambda ^ 2 * Vslow := by
    nlinarith
  have hminPos : 0 < min gammaFast gammaSlow :=
    lt_min hgammaFast hgammaSlow
  have hscaledCoord :
      (min gammaFast gammaSlow / Ccoord) * ‖u‖ ^ 2 ≤
        min gammaFast gammaSlow *
          (S ^ 2 + (B.w * lambda) ^ 2) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hCcoord).2
    have hmul := mul_le_mul_of_nonneg_left hcoord hminPos.le
    dsimp only [S] at hmul ⊢
    nlinarith
  rw [← B.exactSchurCovarianceOperator_quadratic]
  rw [hdecomp]
  exact hscaledCoord.trans hsum

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMainFastSlowCoordinates -/
section


/-!
# Concrete main-coordinate bound for the fast/slow Schur split

This file discharges the finite coordinate comparison left explicit by
`exactSchurGap_of_fastSlow`.  The constant is literal and finite; it may
depend on the fixed arithmetic partition, but it is chosen before the ODE
and no continuum or asymptotic assertion enters its proof.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem gaugeCenterSquareSum_nonneg : 0 ≤ B.gaugeCenterSquareSum := by
  unfold gaugeCenterSquareSum
  exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactSchurFastSlowCoercivity -/
section


/-!
# Closed finite fast/slow coercivity connector

The actual band inverse, the compensated slow variance, and the proved
first-stage regression bound now imply the literal augmented main Schur gap.
No Schur coercivity or coordinate-comparison conclusion remains as a
hypothesis.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

theorem exactSchurGap_of_fastSlow_of_regressionBound
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Creg : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    ∀ u,
      (min gammaFast gammaSlow /
        (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))) * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) := by
  have hCcoord : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hA := B.gaugeCenterSquareSum_nonneg
    have hC2 : 0 ≤ Creg ^ 2 := sq_nonneg _
    positivity
  apply B.exactSchurGap_of_fastSlow
    xi hgammaNuisance hGamma e he hgammaFast hgammaSlow hCcoord
    hfast hslow
  intro u qFast lambda hq hstored
  exact B.main_norm_sq_le_fastSharp_add_storedSlow
    u qFast (B.actualBandRegression xi hgammaNuisance hGamma e)
      lambda Creg hCreg hreg hq hstored

/-- Full finite covariance gap obtained from the two closed Schur blocks.
This is the actual finite baseline gap which can subsequently be transferred
to a preselected effective tilt box by bounded-density domination. -/
theorem hasCovarianceGap_of_fastSlow_of_regressionBound
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Creg : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    B.vectorFamily.HasCovarianceGap
      (min
          (min gammaFast gammaSlow /
            (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2)))
          gammaNuisance /
        (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)) xi := by
  let gammaMain := min gammaFast gammaSlow /
    (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))
  have hden : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hA := B.gaugeCenterSquareSum_nonneg
    have hC2 : 0 ≤ Creg ^ 2 := sq_nonneg _
    positivity
  have hgammaMain : 0 < gammaMain :=
    div_pos (lt_min hgammaFast hgammaSlow) hden
  have hSchur := B.exactSchurGap_of_fastSlow_of_regressionBound
    xi hgammaNuisance hGamma e he hgammaFast hgammaSlow
      hCreg hfast hslow hreg
  simpa only [gammaMain] using
    B.hasCovarianceGap_of_uniform_exactSchur
      xi gammaMain gammaNuisance hgammaMain hgammaNuisance hGamma hSchur

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

private theorem sum_mainCoord_target {Gauge : Type*} [Fintype Gauge]
    (f : MainCoord Gauge → ℝ) :
    (∑ c : MainCoord Gauge, f c) =
      (∑ j : Gauge, f (.gauge j)) + f .slow := by
  let e : MainCoord Gauge ≃ Gauge ⊕ Unit :=
    { toFun := fun c => match c with
        | .gauge j => Sum.inl j
        | .slow => Sum.inr ()
      invFun := fun s => match s with
        | Sum.inl j => .gauge j
        | Sum.inr _ => .slow
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro s; cases s <;> rfl }
  calc
    (∑ c : MainCoord Gauge, f c) =
        ∑ s : Gauge ⊕ Unit, f (e.symm s) := by
      exact Fintype.sum_equiv e f (fun s => f (e.symm s))
        (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [e]







/-- The projected target row represents exactly the gauge part of the
normalized paper target under the finite arithmetic `D` pairing. -/
theorem bandDPairing_projectedNormalizedTargetBand
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (r : B.RawBandGauge) :
    B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      inner ℝ (B.mainRawSlowLinearEquiv.symm (r, 0))
        (B.mainPart (B.normalizedTarget Delta)) := by
  rw [PiLp.inner_apply]
  change B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (r, 0) c
  rw [sum_mainCoord_target]
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero,
    B.mainPart_gauge]
  rw [show B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      ∑ j : Band, B.harmonicMass j * r.1 j *
        B.normalizedTargetBandRow Delta j by
    unfold projectedNormalizedTargetBand bandDPairing
    exact B.weighted_pairing_projectRawBandVector r
      (B.normalizedTargetBandRow Delta)]
  unfold normalizedTargetBandRow
  have hmass (j : Band) : B.harmonicMass j ≠ 0 :=
    ne_of_gt (B.harmonicMass_pos j)
  have hcancel (j : Band) :
      B.harmonicMass j * r.1 j *
          ((B.L / B.q) * Delta j / B.harmonicMass j) =
        r.1 j * ((B.L / B.q) * Delta j) := by
    field_simp [hmass j]
  simp_rw [hcancel]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band => r.1 j * ((B.L / B.q) * Delta j)) B.lowBand]
  rw [B.rawBandGauge_low_eq]
  simp only [B.normalizedTarget_apply, unscaledTarget, coordScale,
    div_one]
  have hrhs :
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
        (∑ x : B.GaugeIndex,
          r.1 x.1 * ((B.L / B.q) * Delta x.1)) -
          (∑ x : B.GaugeIndex, B.lowRatio x * r.1 x.1) *
            ((B.L / B.q) * Delta B.lowBand) := by
    calc
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
          ∑ x : B.GaugeIndex,
            (r.1 x.1 * ((B.L / B.q) * Delta x.1) -
              (B.lowRatio x * r.1 x.1) *
                ((B.L / B.q) * Delta B.lowBand)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hrhs]
  ring

/-- Full raw/slow pairing with the normalized target.  This extends the
preceding gauge identity by the literal stored slow coordinate. -/
theorem inner_mainRawSlow_symm_normalizedTarget
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (q : B.RawBandGauge) (s : ℝ) :
    inner ℝ (B.mainRawSlowLinearEquiv.symm (q, s))
        (B.mainPart (B.normalizedTarget Delta)) =
      B.bandDPairing q (B.projectedNormalizedTargetBand Delta) +
        s * B.mainPart (B.normalizedTarget Delta) MainCoord.slow := by
  have hband := B.bandDPairing_projectedNormalizedTargetBand Delta q
  rw [PiLp.inner_apply] at hband ⊢
  change
    (∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (q, s) c) = _
  change B.bandDPairing q (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (q, 0) c at hband
  rw [sum_mainCoord_target] at hband ⊢
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero] at hband ⊢
  rw [hband]
  ring































/-- Exact target-only formula for the compensated scalar.  All dependence
on the tilted law occurs through the already constructed first-stage
regression vector. -/
theorem compensatedNormalizedTarget_eq_slow_sub_bandDPairing
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) :
    B.compensatedNormalizedTarget xi hgamma hgap e Delta =
      -B.bandDPairing
          (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow := by
  unfold compensatedNormalizedTarget compensatedMainDirection
  rw [B.inner_mainRawSlow_symm_normalizedTarget]
  have hneg :
      B.bandDPairing (-B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) =
        -B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) := by
    unfold bandDPairing
    simp only [Submodule.coe_neg, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hneg]



































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurMarkedRow -/
section


/-!
# Attaching reciprocal nuisance marked rows to the actual Schur operator

This file performs the finite summations that turn a coordinatewise bound
`|Cov(Z_c,v_p)| <= Cmarked / p` into the two covariance-vector bounds used
by the exact Schur perturbation theorem.  The analytic rate remains a
literal hypothesis; in particular the proof does not replace the required
`O(1/(pL))` estimate by a merely bounded `O(1/p)` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Summing a reciprocal marked-prime estimate over one literal band gives
exactly its harmonic mass. -/
theorem abs_covariance_nuisance_bandScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (c : NuisanceCoord B.HeadIndex) (i : Band)
    {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (B.bandScore i)| ≤
        Cmarked * B.harmonicMass i := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandScore i) =
        ∑ p ∈ B.partition.data.fiber i,
          mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m)) := by
    unfold bandScore
    rw [mu.covariance_sum_right]
  change |mu.covariance Z (B.bandScore i)| ≤ _
  rw [hsum]
  calc
    |∑ p ∈ B.partition.data.fiber i,
        mu.covariance Z
          (fun m ↦ ArithmeticModel.valuation p.1
            (B.sampleData.value m))| ≤
        ∑ p ∈ B.partition.data.fiber i,
          |mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hmarked p
    _ = Cmarked * B.harmonicMass i := by
      change (∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ))) =
          Cmarked * ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ))
      rw [Finset.mul_sum]

















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

/-- The rough-stage band envelope gives an ordinary, not sharp, bound for
the unprojected normalized target row. -/
theorem abs_normalizedTargetBandRow_le_of_envelopes
    [Nonempty Head]
    {C : ℝ} (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta) (j : Band) :
    |B.normalizedTargetBandRow Delta j| ≤ C := by
  have hband := henv.1 j
  have hLq : 0 < B.L / B.q := div_pos B.L_pos B.q_pos
  have hqL : 0 < B.q / B.L := div_pos B.q_pos B.L_pos
  have hH : 0 < B.harmonicMass j := B.harmonicMass_pos j
  unfold normalizedTargetBandRow
  rw [abs_div, abs_mul, abs_of_pos hLq, abs_of_pos hH]
  calc
    (B.L / B.q) * |Delta j| / B.harmonicMass j ≤
        (B.L / B.q) *
            ((B.q / B.L) * C * |B.harmonicMass j|) /
          B.harmonicMass j := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hband hLq.le) hH.le
    _ = C := by
      rw [abs_of_pos hH]
      field_simp [B.L_pos.ne', B.q_pos.ne', hH.ne']

/-- The compensated scalar target coordinate has the same fixed envelope.
The division by `w` is cancelled by the sharper rough-stage scalar bound. -/
theorem abs_normalizedTarget_slow_le_of_envelopes
    [Nonempty Head]
    {C : ℝ} (Delta : Band → ℝ)
    (henv : B.HasTargetEnvelopes C Delta) :
    |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤ C := by
  have hslow := henv.2
  have hLq : 0 < B.L / B.q := div_pos B.L_pos B.q_pos
  have hqL : 0 < B.q / B.L := div_pos B.q_pos B.L_pos
  rw [B.mainPart_slow]
  rw [B.normalizedTarget_slow_apply]
  rw [abs_mul, abs_of_pos hLq, abs_div, abs_of_pos B.w_pos]
  calc
    (B.L / B.q) *
        (|∑ j, B.bandCenter j * Delta j| / B.w) ≤
      (B.L / B.q) *
        (((B.q / B.L) * C * B.w) / B.w) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hslow B.w_pos.le) hLq.le
    _ = C := by
      field_simp [B.L_pos.ne', B.q_pos.ne', B.w_pos.ne']

/-- Exact ordinary projection estimate.  The sole geometric input is the
displayed ratio between the first band moment and
`sum_j H_j alpha_j^2`.  On a permitted regular mesh Lemma 8.4 bounds that
ratio uniformly by the fixed positive interior anchor block. -/
theorem projectRawBandVector_norm_le_of_moment_ratio
    [Nonempty Band]
    (x : Band → ℝ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hx : ∀ j, |x j| ≤ C)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * sharpWeightTotal B.harmonicMass B.bandCenter) :
    ‖B.projectRawBandVector x‖ ≤ (1 + R) * C := by
  let total : ℝ := sharpWeightTotal B.harmonicMass B.bandCenter
  let numerator : ℝ := ∑ j : Band,
    B.harmonicMass j * B.bandCenter j * x j
  have htotal : 0 < total := by
    simpa only [total] using B.sharpBandWeightTotal_pos
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hnum : |numerator| ≤
      C * ∑ j : Band, B.harmonicMass j * B.bandCenter j := by
    dsimp only [numerator]
    calc
      |∑ j : Band, B.harmonicMass j * B.bandCenter j * x j| ≤
          ∑ j : Band,
            |B.harmonicMass j * B.bandCenter j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band,
          C * (B.harmonicMass j * B.bandCenter j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul, abs_of_pos (B.harmonicMass_pos j),
          abs_of_pos (B.bandCenter_pos j)]
        calc
          B.harmonicMass j * B.bandCenter j * |x j| ≤
              (B.harmonicMass j * B.bandCenter j) * C :=
            mul_le_mul_of_nonneg_left (hx j)
              (mul_nonneg (B.harmonicMass_pos j).le
                (B.bandCenter_pos j).le)
          _ = C * (B.harmonicMass j * B.bandCenter j) := by ring
      _ = C * ∑ j : Band,
          B.harmonicMass j * B.bandCenter j := by
        rw [Finset.mul_sum]
  have hmean : |numerator / total| ≤ C * R := by
    rw [abs_div, abs_of_pos htotal]
    calc
      |numerator| / total ≤
          (C * ∑ j : Band,
            B.harmonicMass j * B.bandCenter j) / total :=
        div_le_div_of_nonneg_right hnum htotal.le
      _ ≤ (C * (R * total)) / total := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hC) htotal.le
      _ = C * R := by field_simp [htotal.ne']
  have hbound : 0 ≤ (1 + R) * C :=
    mul_nonneg (by linarith) hC
  change ‖(B.projectRawBandVector x).1‖ ≤ (1 + R) * C
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro j
  rw [Real.norm_eq_abs]
  change |weightedGaugeProjection B.harmonicMass B.bandCenter x j| ≤ _
  unfold weightedGaugeProjection
  change |x j - B.bandCenter j * (numerator / total)| ≤ _
  calc
    |x j - B.bandCenter j * (numerator / total)| ≤
        |x j| + |B.bandCenter j| * |numerator / total| := by
      simpa only [abs_mul] using abs_sub (x j)
        (B.bandCenter j * (numerator / total))
    _ ≤ C + 1 * (C * R) := by
      have hcenter := (B.partition.center_mem_zero_one B.n_gt_one j).2
      rw [abs_of_pos (B.bandCenter_pos j)]
      exact add_le_add (hx j)
        (mul_le_mul hcenter hmean (abs_nonneg _) (by positivity))
    _ = (1 + R) * C := by ring

/-- Target-envelope version of the preceding projection estimate. -/
theorem projectedNormalizedTargetBand_norm_le_of_envelopes
    [Nonempty Head] [Nonempty Band]
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (Delta : Band → ℝ) (henv : B.HasTargetEnvelopes C Delta)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * sharpWeightTotal B.harmonicMass B.bandCenter) :
    ‖B.projectedNormalizedTargetBand Delta‖ ≤ (1 + R) * C := by
  exact B.projectRawBandVector_norm_le_of_moment_ratio
    (B.normalizedTargetBandRow Delta) hC hR
    (B.abs_normalizedTargetBandRow_le_of_envelopes Delta henv)
    hRatio



/-- A reciprocal marked family controls an ordinary-bounded raw band score.
Unlike the sharp version, its finite factor is `sum_j H_j`; this is exactly
the `O(log L / L)` nuisance coefficient used for the fast target in the
paper. -/
theorem nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : B.RawBandGauge) :
    ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖) := by
  have hmass : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    apply Finset.sum_nonneg
    intro j hj
    exact (B.harmonicMass_pos j).le
  have hK : 0 ≤ (Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖ :=
    mul_nonneg (mul_nonneg hCmarked hmass) (norm_nonneg q)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandRegressionScore q) hK
  intro c
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandRegressionScore q) =
        ∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j) := by
    unfold bandRegressionScore
    rw [show (fun m ↦ ∑ j : Band, q.1 j * B.bandScore j m) =
      fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
        q.1 j * B.bandScore j m by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mu.covariance_smul_right]
  change |mu.covariance Z (B.bandRegressionScore q)| ≤ _
  rw [hsum]
  calc
    |∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j)| ≤
        ∑ j : Band, |q.1 j * mu.covariance Z (B.bandScore j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band, ‖q‖ * (Cmarked * B.harmonicMass j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hq : |q.1 j| ≤ ‖q‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1 j
      exact mul_le_mul hq
        (B.abs_covariance_nuisance_bandScore_le_of_marked
          xi c j (fun p ↦ hmarked c p))
        (abs_nonneg _) (norm_nonneg q)
    _ = (Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The ordinary inverse and ordinary target bound discharge the fast
nuisance covariance row from the same reciprocal marked family. -/
theorem targetFast_nuisanceCovarianceVector_norm_le_of_marked_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cmarked CinvOrd Tband : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hCinvOrd : 0 ≤ CinvOrd)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (Delta : Band → ℝ)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked * ∑ j : Band, B.harmonicMass j) *
          (CinvOrd * Tband)) := by
  have hq : ‖e.symm (B.projectedNormalizedTargetBand Delta)‖ ≤
      CinvOrd * Tband :=
    (hinvOrd _).trans
      (mul_le_mul_of_nonneg_left htargetBand hCinvOrd)
  have hraw := B.nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    xi hCmarked hmarked
      (e.symm (B.projectedNormalizedTargetBand Delta))
  have hmass : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    apply Finset.sum_nonneg
    intro j hj
    exact (B.harmonicMass_pos j).le
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hq (mul_nonneg hCmarked hmass))
    (Real.sqrt_nonneg _))

/-- The two nuisance covariance rows needed by the exact two-stage solve
come from one literal marked-prime estimate.  The fast row uses the
ordinary inverse because its target is only bounded in raw sup norm; the
slow row uses the already proved compensated `L¹` estimate.  Thus neither
row is an independent analytic contract in Proposition 8.7. -/
theorem twoStage_nuisanceCovarianceRows_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cmarked CinvOrd Tband CL1 : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hCinvOrd : 0 ≤ CinvOrd)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (Delta : Band → ℝ)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1
      (B.actualBandRegression xi hgamma hgap e) ≤ CL1 * B.w) :
    ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((Cmarked * (∑ j : Band, B.harmonicMass j)) *
            (CinvOrd * Tband)) ∧
      ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgamma hgap e))‖ ≤
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * B.w := by
  constructor
  · exact B.targetFast_nuisanceCovarianceVector_norm_le_of_marked_ordinary
      xi e hCmarked hCinvOrd hinvOrd Delta htargetBand hmarked
  · exact B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi (B.actualBandRegression xi hgamma hgap e)
      hCmarked hmarked hL1

/-- The post-radius marked-row estimates in Proposition 8.7 realize the
two fixed nuisance reserves used by the noncircular speed choice. -/
theorem twoStage_nuisanceCovarianceRows_le_halfReserves
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaN : ℝ} (hgammaN : 0 < gammaN)
    (hgap : ∀ z, gammaN * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Cmarked CinvOrd Tband CL1 gammaSlow A : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hCinvOrd : 0 ≤ CinvOrd)
    (hinvOrd : ∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖)
    (Delta : Band → ℝ)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1
      (B.actualBandRegression xi hgammaN hgap e) ≤ CL1 * B.w)
    (hfastReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((Cmarked * (∑ j : Band, B.harmonicMass j)) *
            (CinvOrd * Tband)) ≤ gammaN / 2)
    (hslowReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1) ≤
        gammaN * gammaSlow / (2 * (1 + A))) :
    ‖B.nuisanceCovarianceVector xi
        (B.bandRegressionScore
          (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
        gammaN * (1 / 2) ∧
      ‖B.nuisanceCovarianceVector xi
        (B.postBandPrimeScore
          (B.actualBandRegression xi hgammaN hgap e))‖ ≤
        gammaN * (gammaSlow * B.w / (2 * (1 + A))) := by
  obtain ⟨hfast, hslow⟩ :=
    B.twoStage_nuisanceCovarianceRows_le_of_marked
      xi hgammaN hgap e hCmarked hCinvOrd hinvOrd Delta
      htargetBand hmarked hL1
  constructor
  · exact hfast.trans (hfastReserve.trans_eq (by ring))
  · calc
      ‖B.nuisanceCovarianceVector xi
          (B.postBandPrimeScore
            (B.actualBandRegression xi hgammaN hgap e))‖ ≤
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * B.w := hslow
      _ ≤ (gammaN * gammaSlow / (2 * (1 + A))) * B.w :=
        mul_le_mul_of_nonneg_right hslowReserve B.w_pos.le
      _ = gammaN * (gammaSlow * B.w / (2 * (1 + A))) := by ring

/-- Mixed pairing estimate used by the target numerator: the regression
vector is sharp, while the projected fast target is only ordinary bounded.
The exact arithmetic first moment `sum_j H_j alpha_j` is retained. -/
theorem abs_bandDPairing_le_sharp_mul_raw
    [Nonempty Band]
    (q r : B.RawBandGauge) :
    |B.bandDPairing q r| ≤
      (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
  have hq (j : Band) :
      |q.1 j| ≤ B.bandCenter j *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q := by
    have h := abs_raw_coordinate_le_paperSharpNorm
      B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q j
    simpa only [abs_of_pos (B.bandCenter_pos j)] using h
  have hr (j : Band) : |r.1 j| ≤ ‖r‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm r.1 j
  have hsharp : 0 ≤ paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q := norm_nonneg _
  have hrnorm : 0 ≤ ‖r‖ := norm_nonneg _
  calc
    |B.bandDPairing q r| ≤
        ∑ j : Band, |B.harmonicMass j * q.1 j * r.1 j| := by
      unfold bandDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band,
        (B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_pos (B.harmonicMass_pos j)]
      have hleft : 0 ≤ B.harmonicMass j := (B.harmonicMass_pos j).le
      calc
        B.harmonicMass j * |q.1 j| * |r.1 j| ≤
            B.harmonicMass j *
                (B.bandCenter j *
                  paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q) *
              ‖r‖ := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hq j) hleft)
            (hr j) (abs_nonneg _)
            (mul_nonneg hleft
              (mul_nonneg (B.bandCenter_pos j).le hsharp))
        _ = (B.harmonicMass j * B.bandCenter j) *
              paperSharpNorm B.harmonicMass B.bandCenter
                (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
          ring
    _ = (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q * ‖r‖ := by
      rw [Finset.sum_mul, Finset.sum_mul]





/-- A sharp slow-regression estimate and an ordinary fast-target estimate
bound the compensated scalar target.  No division of the fast target by
`alpha_0` occurs. -/
theorem abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ)
    {Creg Tband TslowCoord : ℝ}
    (hCreg : 0 ≤ Creg)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w)
    (htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband)
    (htargetSlowCoord :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        TslowCoord) :
    |B.compensatedNormalizedTarget xi hgamma hgap e Delta| ≤
      B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband TslowCoord := by
  unfold twoStageCompensatedTargetBoundOrdinaryFast
  rw [B.compensatedNormalizedTarget_eq_slow_sub_bandDPairing]
  have hD := B.abs_bandDPairing_le_sharp_mul_raw
    (B.actualBandRegression xi hgamma hgap e)
    (B.projectedNormalizedTargetBand Delta)
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hregNonneg : 0 ≤ Creg * B.w :=
    mul_nonneg hCreg B.w_pos.le
  have hD' :
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband := by
    calc
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| ≤
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)
            (B.actualBandRegression xi hgamma hgap e) *
          ‖B.projectedNormalizedTargetBand Delta‖ := hD
      _ ≤ (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hreg hmoment)
          htargetBand (norm_nonneg _)
          (mul_nonneg hmoment hregNonneg)
  calc
    |-B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta) +
        B.w * B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
      |B.bandDPairing (B.actualBandRegression xi hgamma hgap e)
          (B.projectedNormalizedTargetBand Delta)| +
        B.w * |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| := by
      calc
        _ ≤ |-B.bandDPairing
              (B.actualBandRegression xi hgamma hgap e)
              (B.projectedNormalizedTargetBand Delta)| +
            |B.w * B.mainPart (B.normalizedTarget Delta)
              MainCoord.slow| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_of_pos B.w_pos]
    _ ≤ (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband + B.w * TslowCoord :=
      add_le_add hD'
        (mul_le_mul_of_nonneg_left htargetSlowCoord B.w_pos.le)





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperHeadPrimeMarkedExact -/
section


/-!
# Exact fixed-head-prime rows

For `p ≤ W`, the canonical head pattern fixes the full `p`-adic valuation
pointwise on every structured cell.  Thus the marked valuation is literally
a function of the finite head tag.  The ODE endpoint preserves its moment
exactly; no moving-prime `C / p` estimate or limiting argument is needed.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A fixed head-prime valuation is exactly the head-tag function carrying
the prescribed exponent. -/
theorem markedValuation_eq_headFunctionScore_of_exactHeadPrimes
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    B.markedValuation p m =
      B.headFunctionScore
        (fun h ↦ ((B.sampleData.pattern h).exponent p : ℝ)) m := by
  have hmem : p ∈
      (B.sampleData.pattern (B.sampleData.cellOf m).1).primes :=
    (hhead (B.sampleData.cellOf m).1 p).2 ⟨hp, hpW⟩
  have hmatch := B.sampleData.value_matches_head m p hmem
  unfold markedValuation headFunctionScore ArithmeticModel.valuation
  simpa only using congrArg (fun k : ℕ ↦ (k : ℝ)) hmatch







/-- Each nonreference centered head coordinate has zero covariance with the
exact inverse-Jacobian vector field, since the paper target has zero head
coordinates. -/
theorem covariance_centeredHeadScore_vectorField_eq_zero
    [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi)
    (h : B.HeadIndex) :
    B.vectorFamily.scalarFamily.covariance
        (B.centeredHeadScore h)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi = 0 := by
  let x : B.ParamSpace :=
    EuclideanSpace.single (MomentCoord.head h) (1 : ℝ)
  have hi := B.inner_covarianceOperator xi x
    (B.vectorFamily.vectorField (B.targetVector Delta) xi)
  rw [B.covarianceOperator_vectorField xi Delta hgamma hgap] at hi
  simpa only [x, EuclideanSpace.inner_single_left,
    B.normalizedTarget_apply, unscaledTarget, coordScale, div_one,
    zero_mul, mul_zero, B.statistic_apply, rawStatistic,
    FiniteExponentialFamily.score,
    VectorExponentialFamily.scalarFamily,
    innerSL_apply_apply, map_one, one_mul, real_inner_comm] using hi.symm

/-- Consequently every fixed head-prime marked row is identically zero on
the whole covariance-gap box.  This is stronger than a `C / p` bound. -/
theorem covariance_headPrimeMarkedValuation_vectorField_eq_zero
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi)
    {p : ℕ} (hp : p.Prime) (hpW : p ≤ B.sampleData.W) :
    B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi = 0 := by
  let phi : Head → ℝ := fun h ↦
    ((B.sampleData.pattern h).exponent p : ℝ)
  let Y : B.sampleData.Sample → ℝ := fun m ↦
    B.vectorFamily.scalarFamily.score m
      (B.vectorFamily.vectorField (B.targetVector Delta) xi)
  let cphi : ℝ := phi B.referenceHead +
    ∑ h : B.HeadIndex,
      (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1
  have hpoint : B.markedValuation p = B.headFunctionScore phi := by
    funext m
    exact B.markedValuation_eq_headFunctionScore_of_exactHeadPrimes
      hhead hp hpW m
  rw [hpoint]
  have hdecomp : B.headFunctionScore phi = fun m ↦
      cphi +
        ∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) *
            B.centeredHeadScore h m := by
    funext m
    rw [B.headFunctionScore_decomposition phi m]
    dsimp only [cphi]
    rw [add_assoc]
    apply congrArg (fun r : ℝ ↦ phi B.referenceHead + r)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    unfold centeredHeadScore
    ring
  rw [hdecomp]
  let mu : FiniteProbability B.sampleData.Sample := B.tiltedLaw xi
  change mu.covariance
      (fun m ↦ cphi +
        ∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) *
            B.centeredHeadScore h m) Y = 0
  rw [mu.covariance_add_left]
  have hconst : mu.covariance (fun _ ↦ cphi) Y = 0 := by
    unfold FiniteProbability.covariance
    have hexpect : mu.expect (fun _ ↦ cphi) = cphi := by
      unfold FiniteProbability.expect
      rw [← Finset.sum_mul, mu.mass_sum]
      ring
    rw [show (fun omega ↦ cphi * Y omega) =
        (fun omega ↦ cphi * Y omega) by rfl,
      mu.expect_smul, hexpect]
    ring
  rw [hconst, zero_add]
  rw [mu.covariance_sum_left]
  apply Finset.sum_eq_zero
  intro h hh
  rw [mu.covariance_smul_left]
  have hz := B.covariance_centeredHeadScore_vectorField_eq_zero
    xi Delta hgamma hgap h
  simpa only [Y, mul_zero] using congrArg
    (fun r : ℝ ↦ (phi h.1 - phi B.referenceHead) * r) hz


end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeAnchorEventually -/
section


/-!
# Literal prime anchors for a fixed regular-mesh block

The continuum anchor used by the transferred inverse is not, by itself, the
prime anchor required by the finite Dirichlet argument.  This file constructs
the latter as the union of the literal prime fibers belonging to the selected
positive cells.  It proves both facts needed later:

* every selected prime stays in the prescribed compact subinterval of
  logarithmic coordinates; and
* its `t_p / p` mass is bounded below uniformly in the mesh, provided the
  selected ideal cells have a fixed total-width floor.

The mass comparison is an unconditional two-endpoint PNT estimate.  In
particular, no arithmetic centre is identified with a continuum centre.
-/

open Filter Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer MovingLowMomentQuadrature
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem mem_canonicalPrimeAnchorSet_iff
    {n W : ℕ} {P : Partition n W (Fin (M.cellCount + 1))}
    {anchors : Finset (Fin M.cellCount)} {p : BandPrime n W} :
    p ∈ canonicalPrimeAnchorSet M P anchors ↔
      ∃ k ∈ anchors, P.band p = positiveBand M k := by
  classical
  simp only [canonicalPrimeAnchorSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map]
  constructor
  · rintro ⟨k, hk, hkp⟩
    exact ⟨k, hk, hkp.symm⟩
  · rintro ⟨k, hk, hpk⟩
    exact ⟨k, hk, hpk.symm⟩

/-- The `t_p/p` mass of one literal fiber is exactly `H_j alpha_j`.
This is finite arithmetic centering, with no limiting object involved. -/
theorem sum_primeWeight_fiber_eq_mass_mul_center
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (j : Fin (M.cellCount + 1)) :
    (∑ p ∈ P.data.fiber j, primeWeight n p) =
      P.mass j * P.center j := by
  have hrewrite : (∑ p ∈ P.data.fiber j, primeWeight n p) =
      ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    unfold primeWeight
    ring
  rw [hrewrite]
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * tPrime n p.1) =
    P.data.mass j *
      ((∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
  field_simp [ne_of_gt (P.data.mass_pos j)]

/-- Exact mass identity for the whole selected prime block. -/
theorem anchorMass_canonicalPrimeAnchorSet_eq
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (anchors : Finset (Fin M.cellCount)) :
    anchorMass (primeWeight n) (canonicalPrimeAnchorSet M P anchors) =
      ∑ k ∈ anchors,
        P.mass (positiveBand M k) * P.center (positiveBand M k) := by
  classical
  unfold anchorMass canonicalPrimeAnchorSet
  rw [← Finset.sum_fiberwise_eq_sum_filter Finset.univ
    (anchors.map (positiveBandEmbedding M)) P.band (primeWeight n)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  exact sum_primeWeight_fiber_eq_mass_mul_center M P (positiveBand M k)

/-- The interior prime mass controls the literal arithmetic centre energy.
This is an exact finite inequality; it does not pass through continuum
centres. -/
theorem epsilon_mul_anchorMass_le_centerEnergy
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) :
    epsilon * anchorMass (primeWeight n)
        (canonicalPrimeAnchorSet M P anchors) ≤ P.centerEnergy := by
  classical
  have hCenterLower (k : Fin M.cellCount) (hk : k ∈ anchors) :
      epsilon ≤ P.center (positiveBand M k) := by
    exact (P.center_mem_of_coord_bounds (positiveBand M k) (fun p hp ↦ by
      apply hinterior p
      exact (mem_canonicalPrimeAnchorSet_iff M).mpr
        ⟨k, hk,
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp⟩)).1
  rw [anchorMass_canonicalPrimeAnchorSet_eq M]
  have hSelected :
      epsilon * (∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k)) ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) *
            P.center (positiveBand M k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hmass := (P.data.mass_pos (positiveBand M k)).le
    have hcenter : 0 ≤ P.center (positiveBand M k) :=
      hepsilon.trans (hCenterLower k hk)
    have hdiff : 0 ≤ P.center (positiveBand M k) - epsilon :=
      sub_nonneg.mpr (hCenterLower k hk)
    nlinarith [mul_nonneg (mul_nonneg hmass hcenter) hdiff]
  calc
    epsilon * (∑ k ∈ anchors,
        P.mass (positiveBand M k) * P.center (positiveBand M k)) ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) *
            P.center (positiveBand M k) := hSelected
    _ = ∑ j ∈ anchors.map (positiveBandEmbedding M),
          P.mass j * P.center j * P.center j := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j,
          P.mass j * P.center j * P.center j := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro j
      exact mul_nonneg
        (mul_nonneg (P.data.mass_pos j).le
          (P.center_mem_zero_one hn j).1)
        (P.center_mem_zero_one hn j).1
    _ = P.centerEnergy := by
      rfl











end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

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

/- Source module: Erdos390.Full.RegularRelativeMeshInteriorAnchors -/
section


/-!
# A fixed-mass interior anchor block in every fine relative mesh

For the uniform moving-low inverse one cannot anchor on a single cell: its
width may tend to zero as the mesh is refined.  This file selects all cells
between the first crossings of `1/4` and `3/4`.  If every cell is shorter
than `1/16` and the low endpoint is below `1/16`, that block lies strictly
inside `[1/8,7/8]` and has total width at least `1/4` (in fact at least
`7/16`).
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem strictMono_endpoint (hdelta : 0 < delta) :
    StrictMono M.endpoint := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [M.endpoint_succ]
  have he := M.endpoint_pos hdelta k
  have hr := M.ratio_pos
  nlinarith [mul_pos he hr]





theorem firstEndpointAtLeast_spec (x : ℝ) (hx : x ≤ 1) :
    x ≤ M.endpoint (M.firstEndpointAtLeast x hx) := by
  exact Nat.find_spec (M.exists_endpoint_ge x hx)



theorem endpoint_lt_of_lt_firstEndpointAtLeast
    (x : ℝ) (hx : x ≤ 1) {k : ℕ}
    (hk : k < M.firstEndpointAtLeast x hx) :
    M.endpoint k < x := by
  exact lt_of_not_ge
    (Nat.find_min (M.exists_endpoint_ge x hx) hk)

theorem firstEndpointAtLeast_pos
    (x : ℝ) (hx : x ≤ 1)
    (hdeltax : delta < x) :
    0 < M.firstEndpointAtLeast x hx := by
  by_contra h
  have hzero : M.firstEndpointAtLeast x hx = 0 := by omega
  have hspec := M.firstEndpointAtLeast_spec x hx
  rw [hzero, M.endpoint_zero] at hspec
  linarith

theorem firstEndpointAtLeast_endpoint_lt_add
    (x tol : ℝ) (hx : x ≤ 1)
    (hdeltax : delta < x)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < tol) :
    M.endpoint (M.firstEndpointAtLeast x hx) < x + tol := by
  let j := M.firstEndpointAtLeast x hx
  have hjpos : 0 < j := M.firstEndpointAtLeast_pos x hx hdeltax
  have hjle : j ≤ M.cellCount := M.firstEndpointAtLeast_le_cellCount x hx
  let k : Fin M.cellCount := ⟨j - 1, by omega⟩
  have hprev : M.endpoint (j - 1) < x := by
    apply M.endpoint_lt_of_lt_firstEndpointAtLeast x hx
    omega
  have hupper : M.upper k = M.endpoint j := by
    dsimp only [k, upper]
    rw [Nat.sub_add_cancel hjpos]
  have hstep : M.endpoint j = M.lower k + M.width k := by
    rw [← hupper]
    unfold width
    ring
  rw [hstep]
  have hw := hwidth k
  dsimp only [k, lower] at hprev ⊢
  linarith



theorem first_quarter_lt_first_threeQuarter
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num) <
      M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num) := by
  let j := M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  have hjUpper : M.endpoint j < (1 / 4 : ℝ) + 1 / 16 := by
    exact M.firstEndpointAtLeast_endpoint_lt_add
      (1 / 4 : ℝ) (1 / 16 : ℝ) (by norm_num)
      (by linarith) hwidth
  have hlLower : (3 / 4 : ℝ) ≤ M.endpoint l :=
    M.firstEndpointAtLeast_spec _ _
  by_contra h
  have hlj : l ≤ j := Nat.le_of_not_gt h
  have hmono := (M.strictMono_endpoint hdelta).monotone hlj
  linarith

theorem interiorAnchors_nonempty
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    M.interiorAnchors.Nonempty := by
  let j := M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  have hjl : j < l :=
    M.first_quarter_lt_first_threeQuarter hdelta hdeltaSmall hwidth
  have hlcell : l ≤ M.cellCount :=
    M.firstEndpointAtLeast_le_cellCount _ _
  let k : Fin M.cellCount := ⟨j, by omega⟩
  refine ⟨k, ?_⟩
  simp only [interiorAnchors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨le_rfl, hjl⟩

theorem interiorAnchors_idealLower
    (hdelta : 0 < delta) {k : Fin M.cellCount}
    (hk : k ∈ M.interiorAnchors) :
    (1 / 8 : ℝ) < M.lower k := by
  have hk' := (Finset.mem_filter.mp hk).2.1
  have hspec := M.firstEndpointAtLeast_spec (1 / 4 : ℝ) (by norm_num)
  have hmono := (M.strictMono_endpoint hdelta).monotone hk'
  dsimp only [lower]
  linarith

theorem interiorAnchors_idealUpper
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ))
    {k : Fin M.cellCount} (hk : k ∈ M.interiorAnchors) :
    M.upper k ≤ 1 - (1 / 8 : ℝ) := by
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  have hklt : k.1 < l := (Finset.mem_filter.mp hk).2.2
  have hlUpper : M.endpoint l < (3 / 4 : ℝ) + 1 / 16 := by
    exact M.firstEndpointAtLeast_endpoint_lt_add
      (3 / 4 : ℝ) (1 / 16 : ℝ) (by norm_num)
      (by linarith) hwidth
  have hsucc : k.1 + 1 ≤ l := by omega
  have hmono := (M.strictMono_endpoint hdelta).monotone hsucc
  dsimp only [upper]
  linarith

theorem sum_width_interiorAnchors_eq
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    (∑ k ∈ M.interiorAnchors, M.width k) =
      M.endpoint
          (M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)) -
      M.endpoint
          (M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)) := by
  let j := M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)
  let l := M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)
  simp only [interiorAnchors, Finset.sum_filter]
  change (∑ a : Fin M.cellCount,
    if j ≤ a.1 ∧ a.1 < l then M.width a else 0) =
      M.endpoint l - M.endpoint j
  simp only [width, upper, lower]
  change (∑ a : Fin M.cellCount,
    (fun i : ℕ ↦ if j ≤ i ∧ i < l then
      M.endpoint (i + 1) - M.endpoint i else 0) a.1) =
        M.endpoint l - M.endpoint j
  have hjl : j < l :=
    M.first_quarter_lt_first_threeQuarter hdelta hdeltaSmall hwidth
  have hlcell : l ≤ M.cellCount :=
    M.firstEndpointAtLeast_le_cellCount _ _
  calc
    _ = ∑ i ∈ Finset.range M.cellCount,
        if j ≤ i ∧ i < l then
          M.endpoint (i + 1) - M.endpoint i else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ if j ≤ i ∧ i < l then
          M.endpoint (i + 1) - M.endpoint i else 0) M.cellCount
    _ = ∑ i ∈ Finset.Ico j l,
        (M.endpoint (i + 1) - M.endpoint i) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro i hi
        rfl
    _ = M.endpoint l - M.endpoint j := by
      rw [Finset.sum_Ico_eq_sub _ hjl.le,
        Finset.sum_range_sub, Finset.sum_range_sub]
      ring

theorem interiorAnchors_mass_lower
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    (1 / 8 : ℝ) ≤ (∑ k ∈ M.interiorAnchors, M.width k) / 2 := by
  have hsum := M.sum_width_interiorAnchors_eq hdelta hdeltaSmall hwidth
  have hlower : (3 / 4 : ℝ) ≤
      M.endpoint (M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)) :=
    M.firstEndpointAtLeast_spec _ _
  have hupper :
      M.endpoint (M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num)) <
        (1 / 4 : ℝ) + 1 / 16 := by
    exact M.firstEndpointAtLeast_endpoint_lt_add
      (1 / 4 : ℝ) (1 / 16 : ℝ) (by norm_num)
      (by linarith) hwidth
  rw [hsum]
  linarith

/-- Every sufficiently fine relative mesh carries the fixed interior anchor
block needed by the mesh-uniform continuum and arithmetic inverse. -/
theorem exists_interiorAnchorBlock
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    ∃ anchors : Finset (Fin M.cellCount), ∃ anchor : Fin M.cellCount,
      anchor ∈ anchors ∧
      (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) ∧
      (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) ∧
      (1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2 := by
  have hne := M.interiorAnchors_nonempty hdelta hdeltaSmall hwidth
  let anchor : Fin M.cellCount := hne.choose
  have hanchor : anchor ∈ M.interiorAnchors := hne.choose_spec
  refine ⟨M.interiorAnchors, anchor, hanchor, ?_, ?_, ?_⟩
  · intro k hk
    exact M.interiorAnchors_idealLower hdelta hk
  · intro k hk
    exact M.interiorAnchors_idealUpper hdelta hdeltaSmall hwidth hk
  · exact M.interiorAnchors_mass_lower hdelta hdeltaSmall hwidth

end Mesh

end

end Erdos390.Full.RegularRelativeMesh

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

/- Source module: Erdos390.Full.PaperProposition87SpeedRadius -/
section


/-!
# Noncircular speed, radius, and eventual slack choices for Proposition 8.7

These are purely quantitative closure lemmas.  All structural bounds are
fixed first; the effective ODE speed is their maximum, and the box radius is
four times that speed.  The ambient threshold is then increased.  No bound
is inferred from an already constructed path.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The mixed-norm compensated target is `w` times a structural constant.
This is the cancellation that prevents the moving low-cell scale from
entering the later ODE box. -/
theorem twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
    {Creg Tband Tslow K : ℝ}
    (hCreg : 0 ≤ Creg) (hTband : 0 ≤ Tband)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ K) :
    B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband Tslow ≤
      B.w * (K * Creg * Tband + Tslow) := by
  unfold twoStageCompensatedTargetBoundOrdinaryFast
  have hw : 0 ≤ B.w := B.w_pos.le
  have hprod : 0 ≤ Creg * B.w * Tband := by positivity
  calc
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband + B.w * Tslow ≤
        K * (Creg * B.w) * Tband + B.w * Tslow := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmoment
            (mul_nonneg hCreg hw)) hTband) le_rfl
    _ = B.w * (K * Creg * Tband + Tslow) := by ring

/-- After writing the compensated prime and nuisance rows as `Cc*w` and
`Cz*w`, all three inverse-speed contributions are bounded independently of
`w`.  This is the exact algebra behind the parameter order
`W -> box -> n`. -/
theorem twoStage_uniform_speed_bounds_of_scaled_rows
    {Creg Tband Tslow K gamma Cc Cz Cord Cfast : ℝ}
    (hCreg : 0 ≤ Creg) (hTband : 0 ≤ Tband)
    (hgamma : 0 < gamma) (hCc : 0 ≤ Cc) (hCz : 0 ≤ Cz)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ K) :
    let A := K * Creg * Tband + Tslow
    Cord * Tband +
        (B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2)) * (Cc * B.w) ≤
          Cord * Tband + (A / gamma) * Cc ∧
      Cfast +
        (B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2)) * (Cz * B.w) ≤
          Cfast + (A / gamma) * Cz ∧
      B.w *
        (B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2)) ≤ A / gamma := by
  dsimp only
  let A : ℝ := K * Creg * Tband + Tslow
  have hstage := B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
    (Tslow := Tslow) hCreg hTband hmoment
  have hden : 0 < gamma * B.w ^ 2 :=
    mul_pos hgamma (sq_pos_of_pos B.w_pos)
  have hquot :
      B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2) ≤
        (B.w * A) / (gamma * B.w ^ 2) :=
    div_le_div_of_nonneg_right hstage hden.le
  have hCcW : 0 ≤ Cc * B.w := mul_nonneg hCc B.w_pos.le
  have hCzW : 0 ≤ Cz * B.w := mul_nonneg hCz B.w_pos.le
  have hPrime := mul_le_mul_of_nonneg_right hquot hCcW
  have hNuisance := mul_le_mul_of_nonneg_right hquot hCzW
  have hSlow := mul_le_mul_of_nonneg_left hquot B.w_pos.le
  have hPrimeCancel :
      ((B.w * A) / (gamma * B.w ^ 2)) * (Cc * B.w) =
        (A / gamma) * Cc := by
    field_simp [B.w_pos.ne', hgamma.ne']
  have hNuisanceCancel :
      ((B.w * A) / (gamma * B.w ^ 2)) * (Cz * B.w) =
        (A / gamma) * Cz := by
    field_simp [B.w_pos.ne', hgamma.ne']
  have hSlowCancel :
      B.w * ((B.w * A) / (gamma * B.w ^ 2)) = A / gamma := by
    field_simp [B.w_pos.ne', hgamma.ne']
  refine ⟨?_, ?_, ?_⟩
  · simpa only [A] using
      add_le_add (le_refl (Cord * Tband))
        (hPrime.trans_eq hPrimeCancel)
  · simpa only [A] using
      add_le_add (le_refl Cfast)
        (hNuisance.trans_eq hNuisanceCancel)
  · exact hSlow.trans_eq hSlowCancel

/-- A unit nuisance reserve suffices after the radius is fixed.  Reserve
one half for the fast nuisance coefficient and require the slow nuisance
coefficient to be at most
`gamma * w / (2 * (1 + A))`.  Since the compensated target is at most
`w*A`, the slow contribution is at most `A/(2(1+A)) ≤ 1/2`.

The small covariance-row estimates which realize these two reserves are
chosen only after the radius-dependent nuisance gap is fixed. -/
theorem twoStage_nuisance_speed_le_one_of_half_reserves
    {Tstage A gamma : ℝ}
    (hA : 0 ≤ A) (hgamma : 0 < gamma)
    (hstage : Tstage ≤ B.w * A) :
    (1 / 2 : ℝ) +
        (Tstage / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) ≤ 1 := by
  have hden : 0 < gamma * B.w ^ 2 :=
    mul_pos hgamma (sq_pos_of_pos B.w_pos)
  have hreserveDen : 0 < 2 * (1 + A) := by positivity
  have hslowReserve : 0 ≤ gamma * B.w / (2 * (1 + A)) := by
    exact div_nonneg (mul_nonneg hgamma.le B.w_pos.le) hreserveDen.le
  have hquot :
      Tstage / (gamma * B.w ^ 2) ≤
        (B.w * A) / (gamma * B.w ^ 2) :=
    div_le_div_of_nonneg_right hstage hden.le
  have hmul := mul_le_mul_of_nonneg_right hquot hslowReserve
  have hcancel :
      ((B.w * A) / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) =
        A / (2 * (1 + A)) := by
    field_simp [B.w_pos.ne', hgamma.ne', hreserveDen.ne']
  have hhalf : A / (2 * (1 + A)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hreserveDen).2
    nlinarith
  calc
    (1 / 2 : ℝ) +
        (Tstage / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) ≤
      1 / 2 +
        ((B.w * A) / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) := add_le_add le_rfl hmul
    _ = 1 / 2 + A / (2 * (1 + A)) := by rw [hcancel]
    _ ≤ 1 := by linarith

end BridgeData



/-- Noncircular version used in the paper.  Only the box-independent prime
and stored-slow bounds enter the choice.  A unit reserve is built in for the
nuisance component; after this radius is fixed, the marked nuisance rate is
made smaller than that reserve by increasing `n`. -/
theorem exists_speed_radius_before_vanishing_nuisance
    (prime slow : ℝ) :
    ∃ speed a : NNReal,
      1 ≤ (speed : ℝ) ∧
      prime ≤ (speed : ℝ) ∧
      slow ≤ (speed : ℝ) ∧
      speed ≤ a ∧
      (a : ℝ) = 4 * (speed : ℝ) := by
  let M : ℝ := max 1 (max prime slow)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans
    (le_max_left 1 (max prime slow))
  let speed : NNReal := ⟨M, hM⟩
  let a : NNReal := 4 * speed
  refine ⟨speed, a, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · exact (le_max_left prime slow).trans (le_max_right 1 _)
  · exact (le_max_right prime slow).trans (le_max_right 1 _)
  · dsimp only [a]
    exact le_mul_of_one_le_left (show 0 ≤ speed from zero_le) (by norm_num)
  · rfl

/-- Every constant depending on the already fixed effective box may multiply
a vanishing row rate without feeding back into the box choice. -/
theorem eventually_const_mul_vanishing_rate_le
    (rate : ℕ → ℝ) (K reserve : ℝ)
    (hrate : Tendsto rate atTop (nhds 0))
    (hreserve : 0 < reserve) :
    ∀ᶠ n : ℕ in atTop, K * rate n ≤ reserve := by
  have hscaled : Tendsto (fun n : ℕ ↦ K * rate n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrate
  exact hscaled.eventually (eventually_le_nhds hreserve)

/-- Once all constants and the radius are fixed, the logarithmic ambient
slack inequality used by the feasibility ledger holds eventually. -/
theorem eventually_fixed_exponential_slack_le_L
    (Cfixed K Cactive : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Cfixed + Real.exp K * Cactive ≤ Scale.L n := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hLTop.eventually
    (eventually_ge_atTop (Cfixed + Real.exp K * Cactive))

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

/-- Algebraic comparison of the ordinary fast marked-row majorant with the
sharp rate `epsilon * log L`. -/
theorem fastMarkedRowMajorant_le_of_harmonicMass
    (B : BridgeData Head Band)
    {epsilon CinvOrd Tband logL droot : ℝ}
    (hepsilon : 0 ≤ epsilon) (hCinvOrd : 0 ≤ CinvOrd)
    (hTband : 0 ≤ Tband) (hdroot : 0 ≤ droot)
    (hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot)
    (hmass : (∑ j : Band, B.harmonicMass j) ≤ 12 * logL) :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((epsilon * (∑ j : Band, B.harmonicMass j)) *
          (CinvOrd * Tband)) ≤
      (12 * droot * CinvOrd * Tband) * (epsilon * logL) := by
  have hmassNonneg : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    exact Finset.sum_nonneg fun j hj ↦ (B.harmonicMass_pos j).le
  have hepsMass : 0 ≤ epsilon *
      (∑ j : Band, B.harmonicMass j) :=
    mul_nonneg hepsilon hmassNonneg
  have hcoef : 0 ≤ droot * CinvOrd * Tband := by positivity
  have hcoefCompare :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          CinvOrd * Tband ≤ droot * CinvOrd * Tband := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdimension hCinvOrd) hTband
  have hscaled :
      epsilon * (∑ j : Band, B.harmonicMass j) ≤
        epsilon * (12 * logL) :=
    mul_le_mul_of_nonneg_left hmass hepsilon
  calc
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((epsilon * (∑ j : Band, B.harmonicMass j)) *
          (CinvOrd * Tband)) =
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        CinvOrd * Tband) *
          (epsilon * (∑ j : Band, B.harmonicMass j)) := by ring
    _ ≤ (droot * CinvOrd * Tband) *
          (epsilon * (∑ j : Band, B.harmonicMass j)) :=
      mul_le_mul_of_nonneg_right hcoefCompare hepsMass
    _ ≤ (droot * CinvOrd * Tband) * (epsilon * (12 * logL)) :=
      mul_le_mul_of_nonneg_left hscaled hcoef
    _ = _ := by ring

/-- Uniform eventual smallness of the ordinary fast nuisance row.  The
fixed reserve may depend on the radius already chosen, but it does not feed
back into that choice. -/
theorem eventually_fastMarkedRowMajorant_le
    (W : ℕ) (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    {CinvOrd Tband reserve : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hreserve : 0 < reserve) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            ((epsilon B.sampleData.n *
              (∑ j : Band, B.harmonicMass j)) *
                (CinvOrd * Tband)) ≤ reserve := by
  let droot : ℝ := nuisanceDimensionCeiling Head
  let K : ℝ := 12 * droot * CinvOrd * Tband
  have hsmall := eventually_const_mul_vanishing_rate_le
    (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n)) K reserve
      hepsilonRate hreserve
  filter_upwards [eventually_sum_harmonicMass_le_twelve_logL
      (Head := Head) (Band := Band) W, hsmall] with n hmass hsmallN
  intro B hBn hBW
  have hmajor := fastMarkedRowMajorant_le_of_harmonicMass
    (droot := droot) B
    (hepsilonNonneg B.sampleData.n) hCinvOrd hTband
    (by exact Real.sqrt_nonneg _)
    (by simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling)
    (hmass B hBn hBW)
  have hsmallB :
      (12 * droot * CinvOrd * Tband) *
          (epsilon B.sampleData.n * Real.log (Scale.L B.sampleData.n)) ≤
        reserve := by
    simpa only [hBn, K] using hsmallN
  exact hmajor.trans hsmallB

/-- The compensated slow nuisance row has no harmonic loss.  Its marked
coefficient is eventually smaller than any fixed post-radius reserve. -/
theorem eventually_slowMarkedRowCoefficient_le
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    {CL1 reserve : ℝ} (hCL1 : 0 ≤ CL1) (hreserve : 0 < reserve) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band), B.sampleData.n = n →
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (epsilon B.sampleData.n * CL1) ≤ reserve := by
  have hepsilon : Tendsto epsilon atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero epsilon
      hepsilonNonneg hepsilonRate
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hscaled : Tendsto (fun n : ℕ ↦
      (droot * CL1) * epsilon n) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hepsilon
  have hevent := hscaled.eventually (eventually_le_nhds hreserve)
  filter_upwards [hevent] with n hn
  intro B hBn
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling
  have hepsCL1 : 0 ≤ epsilon B.sampleData.n * CL1 :=
    mul_nonneg (hepsilonNonneg B.sampleData.n) hCL1
  calc
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (epsilon B.sampleData.n * CL1) ≤
      droot * (epsilon B.sampleData.n * CL1) :=
        mul_le_mul_of_nonneg_right hdimension hepsCL1
    _ = (droot * CL1) * epsilon B.sampleData.n := by ring
    _ ≤ reserve := by simpa only [hBn] using hn

/-- Simultaneous post-radius reserves used by the unit nuisance-speed
estimate.  The positive floor `gammaFloor` is fixed only after the ODE
radius; both conclusions then follow by increasing the ambient integer.
The theorem is uniform over every canonical bridge with the displayed
ambient integer and cutoff. -/
theorem eventually_twoStageMarkedRowReserves
    (W : ℕ) (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    {CinvOrd Tband CL1 gammaFloor gammaSlow A : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hCL1 : 0 ≤ CL1) (hgammaFloor : 0 < gammaFloor)
    (hgammaSlow : 0 < gammaSlow) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            ((epsilon B.sampleData.n *
              (∑ j : Band, B.harmonicMass j)) *
                (CinvOrd * Tband)) ≤ gammaFloor / 2 ∧
          Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (epsilon B.sampleData.n * CL1) ≤
            gammaFloor * gammaSlow / (2 * (1 + A)) := by
  have hfastReserve : 0 < gammaFloor / 2 := div_pos hgammaFloor (by norm_num)
  have hslowDen : 0 < 2 * (1 + A) := by positivity
  have hslowReserve :
      0 < gammaFloor * gammaSlow / (2 * (1 + A)) :=
    div_pos (mul_pos hgammaFloor hgammaSlow) hslowDen
  have hfast := eventually_fastMarkedRowMajorant_le
    (Head := Head) (Band := Band) W epsilon hepsilonNonneg
      hepsilonRate hCinvOrd hTband hfastReserve
  have hslow := eventually_slowMarkedRowCoefficient_le
    (Head := Head) (Band := Band) epsilon hepsilonNonneg
      hepsilonRate hCL1 hslowReserve
  filter_upwards [hfast, hslow] with n hfastN hslowN
  intro B hBn hBW
  exact ⟨hfastN B hBn hBW, hslowN B hBn⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalPositiveCellVarianceEventually -/
section


/-!
# Positive-cell variance on an arbitrary regular relative mesh

The moving low cell alone controls the paper scale only when the positive
relative width is no larger than the low endpoint.  This file supplies the
missing complementary estimate: the sum of the literal within-cell prime
variances in the positive cells is bounded below by a fixed multiple of the
square of the actual common mesh ratio.  The proof first identifies the
finite prime moments with three unconditional PNT quadratures and then
passes to the exact continuum cell variance.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)











































/-- The fixed interior prime mass gives a mesh-independent lower floor for
the literal arithmetic centre energy. -/
theorem one_div_64_le_centerEnergy_of_canonical_anchor
    {n W : ℕ} (hdelta : 0 < delta)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors)) :
    (1 : ℝ) / 64 ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergy := epsilon_mul_anchorMass_le_centerEnergy M P hn
    (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hinterior
  calc
    (1 : ℝ) / 64 = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
    _ ≤ (1 / 8 : ℝ) *
        FiniteAnchoredDirichletQuadratic.anchorMass
          (PrimeSquarefreeDirichletGeometry.primeWeight n)
          (canonicalPrimeAnchorSet M P anchors) := by
      exact mul_le_mul_of_nonneg_left hAnchorMass (by norm_num)
    _ ≤ P.centerEnergy := hEnergy



end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually -/
section


/-!
# Paper-scale geometric moment inputs on every permitted fine mesh

This file assembles the arithmetic estimates used after the continuum-to-band
transfer.  The structural prime cutoff and the numerical mesh tolerance are
chosen before the mesh.  The two mesh parameters remain independent: the
only comparison used is the two-sided regularity condition from the paper,
namely

`cMesh * eta ≤ M.ratio ≤ eta`.

The lower variance estimate deliberately combines two different arithmetic
sources.  The moving low cell controls `delta^2`, while the positive cells
control the square of the actual relative width `M.ratio`.  Thus no hidden
hypothesis such as `M.ratio ≤ delta` or `eta ≤ delta` is present.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PaperPermittedRegularMesh

namespace Mesh







/--
The canonical centre energy has an absolute lower floor on every sufficiently
fine paper mesh.  The cutoff is chosen before `delta`, `eta`, and the mesh;
no comparison between the two mesh parameters is required.

This is the denominator estimate used when an ordinary row bound is converted
to the paper's quotient moment ratio.  Stating it separately prevents that
conversion from silently importing the regularity hypothesis needed only for
the variance lower bound.
-/
theorem canonicalPaperCenterEnergyFloorCutoff_eventually :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ canonicalPaperGeometricMeshTolerance →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              (1 : ℝ) / 64 ≤
                (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  intro W hW delta eta M hdelta hfine
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith [M.ratio_le_eta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hIdealLower, hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  have hPrimeAnchor := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hW (epsilon := (1 / 8 : ℝ)) anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hPrimeAnchor] with n hAnchorAt
  obtain ⟨hWne, hn, hAnchorAll⟩ := hAnchorAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hInterior, hAnchorMass⟩ := hAnchorAll S
  exact one_div_64_le_centerEnergy_of_canonical_anchor M hdelta
    hn hWne S anchors hInterior hAnchorMass



end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalMomentRatioEventually -/
section


/-!
# Canonical paper-scale moment-ratio bound

This file discharges the quotient first-moment ratio used by the ordinary
Schur transfer.  The numerator is the literal arithmetic first moment
`sum_j H_j * alpha_j`; the denominator is the literal sharp projection
weight `sum_j H_j * alpha_j^2`.  A canonical interior prime anchor gives a
uniform positive denominator, while the elementary prime-band estimate
bounds the numerator.

All constants are selected before `W`, the two independent mesh parameters,
and the mesh.  The public statement exposes no anchor or analytic estimate.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PaperWeightedInverseExport MovingLowGaugeTransfer
open RegularMeshPrimeCutoffs RegularRelativeMesh

namespace BridgeData

/--
Uniform first-moment/centre-energy ratio for the literal canonical
partition.  The displayed fineness condition is the paper scale
`delta + eta`; no comparison between `delta` and `eta` is assumed.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_momentRatio :
    ∃ Rproj : ℝ, 0 < Rproj ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ meshTol →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          (∃ hWne : B.sampleData.W ≠ 0,
            ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
          (∑ j : Fin (M.cellCount + 1),
              B.harmonicMass j * B.bandCenter j) ≤
            Rproj * sharpWeightTotal B.harmonicMass B.bandCenter := by
  let Rproj : ℝ := 128 * Real.log 4
  have hRproj : 0 < Rproj := by
    dsimp only [Rproj]
    positivity
  refine ⟨Rproj, hRproj,
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance,
    by norm_num [RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance],
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidable _instNonempty
  have hEnergyN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperCenterEnergyFloorCutoff_eventually
      W hW M hdelta hfine
  have hBandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hEnergyN, hBandTN] with n hEnergyAt hBandTAt
  intro B hBn hBW hpartition
  subst n
  subst W
  obtain ⟨hWne, hn, hEnergyAll⟩ := hEnergyAt
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
    hn hWne S
  have hpartitionCanonical : B.partition = P := by
    exact hpartitionUser.trans (by dsimp only [P])
  have hEnergy : (1 : ℝ) / 64 ≤ B.partition.centerEnergy := by
    rw [hpartitionCanonical]
    exact hEnergyAll S
  have hFirstMoment :
      (∑ j : Fin (M.cellCount + 1),
          B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := by
    simpa only [harmonicMass, bandCenter] using
      B.partition.sum_mass_mul_center_eq_bandTReciprocalSum
  have hSharpWeight :
      sharpWeightTotal B.harmonicMass B.bandCenter =
        B.partition.centerEnergy := by
    unfold sharpWeightTotal sharpWeight harmonicMass bandCenter
    unfold ArithmeticBandGeometry.Partition.centerEnergy
      Erdos390.Lemma84.WeightedBandData.centerEnergy
      Erdos390.Lemma84.WeightedBandData.bandNormSq
      Erdos390.Lemma84.WeightedBandData.bandInner
    simp only [pow_two, mul_assoc]
  calc
    (∑ j : Fin (M.cellCount + 1),
        B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := hFirstMoment
    _ ≤ 2 * Real.log 4 := hBandTAt
    _ = Rproj * ((1 : ℝ) / 64) := by
      dsimp only [Rproj]
      ring
    _ ≤ Rproj * B.partition.centerEnergy :=
      mul_le_mul_of_nonneg_left hEnergy hRproj.le
    _ = Rproj * sharpWeightTotal B.harmonicMass B.bandCenter := by
      rw [hSharpWeight]

end BridgeData

end PaperBridgeFit

end Full

end Erdos390

end

end

/- Source module: Erdos390.Full.PaperCanonicalBandFirstMomentEventually -/
section


/-!
# Canonical band first-moment bound

The target and speed packages in Proposition 8.7 use the literal arithmetic
first moment `sum_j H_j * alpha_j`.  It is exactly the reciprocal prime-band
moment, independently of the chosen partition, and hence is eventually at
most `2 * log 4`.  Keeping this elementary conversion in a named terminal
prevents the final orchestration from retaining a moment inequality as an
analytic call-site hypothesis.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- The partition first moment has the universal eventual prime-band bound. -/
theorem eventually_bandFirstMoment_le_two_log_four (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤
          2 * Real.log 4 := by
  filter_upwards [eventually_bandTReciprocalSum_le W] with n hband
  intro B hBn hBW
  subst n
  subst W
  calc
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := by
      simpa only [harmonicMass, bandCenter] using
        B.partition.sum_mass_mul_center_eq_bandTReciprocalSum
    _ ≤ 2 * Real.log 4 := hband

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalTargetPackage -/
section


/-!
# Canonical target package for Proposition 8.7

This file removes the target estimates from the eventual Proposition 8.7
call site.  The rough-stage hypothesis is the literal paper envelope
`HasTargetEnvelopes`.  The ordinary band target is controlled by the
arithmetic moment ratio (not by the vanishing low-cell centre), while the
slow coordinate uses the exact compensated compatibility bound.  The final
estimate records the factor `B.w` needed for a box radius chosen before the
ambient threshold.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- All target conclusions used in Proposition 8.7, derived from the exact
rough-stage envelopes and the two geometric estimates.  In particular,
none of the three displayed target bounds is an independent analytic
assumption. -/
theorem canonicalTwoStageTargetPackage_of_envelopes
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ)
    {Ctarget Rproj Creg K : ℝ}
    (hCtarget : 0 ≤ Ctarget) (hRproj : 0 ≤ Rproj)
    (hCreg : 0 ≤ Creg)
    (henv : B.HasTargetEnvelopes Ctarget Delta)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * sharpWeightTotal B.harmonicMass B.bandCenter)
    (hmoment : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤ K)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w) :
    ‖B.projectedNormalizedTargetBand Delta‖ ≤
        (1 + Rproj) * Ctarget ∧
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        Ctarget ∧
      |B.compensatedNormalizedTarget xi hgamma hgap e Delta| ≤
        B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg ((1 + Rproj) * Ctarget) Ctarget ∧
      B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg ((1 + Rproj) * Ctarget) Ctarget ≤
        B.w *
          (K * Creg * ((1 + Rproj) * Ctarget) + Ctarget) := by
  have htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤
      (1 + Rproj) * Ctarget :=
    B.projectedNormalizedTargetBand_norm_le_of_envelopes
      hCtarget hRproj Delta henv hRatio
  have htargetSlow :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤ Ctarget :=
    B.abs_normalizedTarget_slow_le_of_envelopes Delta henv
  have htargetComp :=
    B.abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
      xi hgamma hgap e Delta hCreg hreg htargetBand htargetSlow
  have hTband : 0 ≤ (1 + Rproj) * Ctarget := by positivity
  have hstage :=
    B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
      (Creg := Creg) (Tband := (1 + Rproj) * Ctarget)
      (Tslow := Ctarget) hCreg hTband hmoment
  exact ⟨htargetBand, htargetSlow, htargetComp, hstage⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalNuisanceReservesEventually -/
section


/-!
# Canonical nuisance reserves for Proposition 8.7

The fast and slow nuisance rows in the finite two-stage assembly are not
independent analytic inputs.  Both follow from the same reciprocal marked
prime row.  This file performs the paper's non-circular choice: first fix
the effective box and hence a positive nuisance-gap floor; only afterwards
increase `n` until the marked row fits the two reserved halves.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport

namespace BridgeData

set_option maxHeartbeats 2000000 in
/-- Eventual canonical realization of the two nuisance reserves consumed by
the exact Proposition 8.7 assembly.  The only score input is the already
proved compensated `L¹` estimate; no nuisance covariance-row hypothesis is
exposed. -/
theorem eventually_canonical_twoStage_nuisance_halfReserves
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W)
    (a : NNReal) (marginFloor : ℝ) (hmargin : 0 < marginFloor)
    {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band]
    {CinvOrd Tband CL1 gammaSlow A : ℝ}
    (hCinvOrd : 0 ≤ CinvOrd) (hTband : 0 ≤ Tband)
    (hCL1 : 0 ≤ CL1) (hgammaSlow : 0 < gammaSlow) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        ∀ (hBWlarge : 1 < B.sampleData.W),
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ c : Cell Head,
            (rawCell Phead I B.sampleData.n c \
              (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
            ∀ (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ)),
              ∀ (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
                (Delta : Band → ℝ),
                (∀ v, ‖e.symm v‖ ≤ CinvOrd * ‖v‖) →
                ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband →
                (let xi := B.effectiveParamEquiv z
                 let gammaN :=
                   B.canonicalEffectiveNuisanceGamma
                     I U (3 * (a : ℝ)) T
                 let hgammaN : 0 < gammaN :=
                   B.canonicalEffectiveNuisanceGamma_pos
                     I U (3 * (a : ℝ)) T
                 let hgap : ∀ v, gammaN * ‖v‖ ^ 2 ≤
                     inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
                   intro v
                   simpa only [xi, gammaN] using
                     B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                       hlowerOne hupperU
                       (by intro sigma; rw [hcanonical]; rfl)
                       (by intro sigma; rw [hcanonical]; rfl)
                       T hbaseline hBWlarge z hz v
                 B.partition.compensatedL1
                     (B.actualBandRegression xi hgammaN hgap e) ≤
                   CL1 * B.w) →
                (let xi := B.effectiveParamEquiv z
                 let gammaN :=
                   B.canonicalEffectiveNuisanceGamma
                     I U (3 * (a : ℝ)) T
                 let hgammaN : 0 < gammaN :=
                   B.canonicalEffectiveNuisanceGamma_pos
                     I U (3 * (a : ℝ)) T
                 let hgap : ∀ v, gammaN * ‖v‖ ^ 2 ≤
                     inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
                   intro v
                   simpa only [xi, gammaN] using
                     B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                       hlowerOne hupperU
                       (by intro sigma; rw [hcanonical]; rfl)
                       (by intro sigma; rw [hcanonical]; rfl)
                       T hbaseline hBWlarge z hz v
                 ‖B.nuisanceCovarianceVector xi
                     (B.bandRegressionScore
                       (e.symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
                     gammaN * (1 / 2) ∧
                   ‖B.nuisanceCovarianceVector xi
                     (B.postBandPrimeScore
                       (B.actualBandRegression xi hgammaN hgap e))‖ ≤
                     gammaN *
                       (gammaSlow * B.w / (2 * (1 + A)))) := by
  obtain ⟨epsilon, hepsilon0, hepsilonRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger
        W hW hHeadLe a
  let gammaFloor : ℝ :=
    canonicalEffectiveNuisanceGammaFloor
      Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmargin
  have hreserves := eventually_twoStageMarkedRowReserves
    (Head := Head) (Band := Band) W epsilon hepsilon0 hepsilonRate
      hCinvOrd hTband hCL1 hgammaFloor hgammaSlow hA
  filter_upwards [hreserves, eventually_ge_atTop Nmarked] with
      n hreservesN hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical T hTmargin
    hbaseline z hz e Delta hinvOrd htargetBand hL1
  subst n
  subst W
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  let gammaN : ℝ :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgammaN : 0 < gammaN := by
    dsimp only [gammaN]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gammaN * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    simpa only [xi, gammaN] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU
        (by intro sigma; rw [hcanonical]; rfl)
        (by intro sigma; rw [hcanonical]; rfl)
        T hbaseline hBWlarge z hz v
  have hfloorLe : gammaFloor ≤ gammaN := by
    dsimp only [gammaFloor, gammaN]
    exact B.canonicalEffectiveNuisanceGammaFloor_le
      I hU (by positivity) hmargin T hTmargin
  obtain ⟨hfastFloor, hslowFloor⟩ := hreservesN B rfl rfl
  have hfastReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((epsilon B.sampleData.n *
              (∑ j : Band, B.harmonicMass j)) *
            (CinvOrd * Tband)) ≤ gammaN / 2 := by
    exact hfastFloor.trans (div_le_div_of_nonneg_right
      hfloorLe (by norm_num))
  have hslowReserve :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (epsilon B.sampleData.n * CL1) ≤
        gammaN * gammaSlow / (2 * (1 + A)) := by
    have hmul : gammaFloor * gammaSlow ≤ gammaN * gammaSlow :=
      mul_le_mul_of_nonneg_right hfloorLe hgammaSlow.le
    exact hslowFloor.trans
      (div_le_div_of_nonneg_right hmul (by positivity))
  have hmarkedAt : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        epsilon B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    simpa only [xi] using
      hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hresult := B.twoStage_nuisanceCovarianceRows_le_halfReserves
    xi hgammaN hgap e (hepsilon0 B.sampleData.n) hCinvOrd
      hinvOrd Delta htargetBand hmarkedAt hL1 hfastReserve hslowReserve
  simpa only [xi, gammaN] using hresult

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalSpeedPackage -/
section


/-!
# Non-circular speed package for Proposition 8.7

All constants entering the fast and slow velocities are fixed before the
effective box.  The speed is the maximum of the two structural bounds and
one unit reserved for the nuisance velocity; the radius is four times that
speed.  The exact finite inequalities are then consequences for every
positive paper scale `B.w`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]



/-- Type- and mesh-uniform form of the same radius choice.  The witnesses
`speed` and `a` are selected before the head type and the regular partition;
all subsequent finite band types use those identical witnesses.  This is the
quantifier order consumed by the paper-level eventual Proposition 8.7. -/
theorem exists_speed_radius_with_canonicalTwoStage_bounds_uniformTypes
    {CinvOrd Tband Creg Tslow K gammaSlow Ccoef : ℝ}
    (hTband : 0 ≤ Tband)
    (hCreg : 0 ≤ Creg) (hTslow : 0 ≤ Tslow)
    (hK : 0 ≤ K) (hgammaSlow : 0 < gammaSlow)
    (hCcoef : 0 ≤ Ccoef) :
    let A := K * Creg * Tband + Tslow
    ∃ speed a : NNReal,
      1 ≤ (speed : ℝ) ∧ speed ≤ a ∧
      (a : ℝ) = 4 * (speed : ℝ) ∧
      ∀ {Head Band : Type*} [Fintype Head] [DecidableEq Head]
        [Fintype Band] [DecidableEq Band],
      ∀ (B : BridgeData Head Band),
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤ K →
        CinvOrd * Tband +
            (B.twoStageCompensatedTargetBoundOrdinaryFast
                Creg Tband Tslow / (gammaSlow * B.w ^ 2)) *
              (Ccoef * B.w) ≤ (speed : ℝ) ∧
          (1 / 2 : ℝ) +
              (B.twoStageCompensatedTargetBoundOrdinaryFast
                Creg Tband Tslow / (gammaSlow * B.w ^ 2)) *
                (gammaSlow * B.w / (2 * (1 + A))) ≤
            (speed : ℝ) ∧
          B.w *
              (B.twoStageCompensatedTargetBoundOrdinaryFast
                Creg Tband Tslow / (gammaSlow * B.w ^ 2)) ≤
            (speed : ℝ) := by
  dsimp only
  let A : ℝ := K * Creg * Tband + Tslow
  let primeBound : ℝ :=
    CinvOrd * Tband + (A / gammaSlow) * Ccoef
  let slowBound : ℝ := A / gammaSlow
  obtain ⟨speed, a, hspeedOne, hprimeSpeed, hslowSpeed,
      hmargin, hradius⟩ :=
    exists_speed_radius_before_vanishing_nuisance primeBound slowBound
  refine ⟨speed, a, hspeedOne, hmargin, hradius, ?_⟩
  intro Head Band _instHeadFintype _instHeadDecidable
    _instBandFintype _instBandDecidable B hmoment
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  obtain ⟨hprime, _hnuisanceScaled, hslow⟩ :=
    B.twoStage_uniform_speed_bounds_of_scaled_rows
      (Creg := Creg) (Tband := Tband) (Tslow := Tslow) (K := K)
      (gamma := gammaSlow) (Cc := Ccoef) (Cz := 0)
      (Cord := CinvOrd) (Cfast := 0)
      hCreg hTband hgammaSlow hCcoef (by norm_num) hmoment
  have hstage :=
    B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
      (Creg := Creg) (Tband := Tband) (Tslow := Tslow)
      hCreg hTband hmoment
  have hnuisance :=
    B.twoStage_nuisance_speed_le_one_of_half_reserves
      hA hgammaSlow hstage
  refine ⟨?_, ?_, ?_⟩
  · exact hprime.trans (by simpa only [primeBound, A] using hprimeSpeed)
  · exact hnuisance.trans hspeedOne
  · exact hslow.trans (by simpa only [slowBound, A] using hslowSpeed)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalFullGap -/
section


/-!
# Full covariance gap from the exact Lemmas 8.4 and 8.6 outputs

This connector eliminates the `HasCovarianceGap` premise used by the marked
row and ODE modules.  A sharp inverse for the literal actual band Schur map
gives the fast quadratic gap; Lemma 8.6 supplies the compensated slow gap
and regression bound.  The finite fast/slow and nuisance Schur identities
then give the full covariance gap.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Exact full covariance gap, with the fast block derived from the inverse
rather than assumed. -/
theorem hasCovarianceGap_of_sameMap_sharpInverse_and_slow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {Cinv gammaSlow Creg : ℝ}
    (hCinv : 0 < Cinv) (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hslow : gammaSlow * B.w ^ 2 ≤
      B.actualTwoStageCompensatedVariance
        xi hgammaNuisance hGamma e)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    0 < B.canonicalTwoStageFullGap
        Cinv gammaSlow Creg gammaNuisance ∧
      B.vectorFamily.HasCovarianceGap
        (B.canonicalTwoStageFullGap
          Cinv gammaSlow Creg gammaNuisance) xi := by
  let gammaFast : ℝ :=
    rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
      (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)
  let gammaMain : ℝ := min gammaFast gammaSlow /
    (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))
  have hgammaFast : 0 < gammaFast := by
    dsimp only [gammaFast]
    exact div_pos
      (sq_pos_of_pos (rawDLowerWeight_pos B.harmonicMass B.bandCenter
        B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one)))
      (mul_pos B.sharpBandWeightTotal_pos hCinv)
  have hcoordDen : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hg := B.gaugeCenterSquareSum_nonneg
    positivity
  have hgammaMain : 0 < gammaMain :=
    div_pos (lt_min hgammaFast hgammaSlow) hcoordDen
  have hfullDen : 0 <
      3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2 := by
    positivity
  have hgammaFull : 0 < B.canonicalTwoStageFullGap
      Cinv gammaSlow Creg gammaNuisance := by
    unfold canonicalTwoStageFullGap
    dsimp only
    exact div_pos (lt_min hgammaMain hgammaNuisance) hfullDen
  have hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)) := by
    intro q
    simpa only [gammaFast] using
      B.actualBandSchur_quadratic_lower_of_inverse_arithmetic
        xi hgammaNuisance hGamma e he hCinv hinv q
  have hslow' : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e) := by
    simpa only [actualTwoStageCompensatedVariance] using hslow
  have hfull := B.hasCovarianceGap_of_fastSlow_of_regressionBound
    xi hgammaNuisance hGamma e he hgammaFast hgammaSlow hCreg
      hfast hslow' hreg
  refine ⟨hgammaFull, ?_⟩
  simpa only [canonicalTwoStageFullGap, gammaFast, gammaMain] using hfull

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87AllPrimeMarkedSplit -/
section


/-!
# Exact split between fixed head primes and moving band primes

The fixed branch `p ≤ W` is killed identically by the head coordinates.
Only the moving branch `W < p ≤ y(n)` uses the analytic marked-row bound.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Combine the exact head-prime row and the analytic moving-prime row.
The hypotheses make the finite split and its quantifiers fully explicit. -/
theorem uniform_allPrime_markedRow_of_exactHead_and_moving
    [Nonempty Head]
    (hhead : ∀ h : Head, ∀ r : ℕ,
      r ∈ (B.sampleData.pattern h).primes ↔
        r.Prime ∧ r ≤ B.sampleData.W)
    (Delta : Band → ℝ) (a : NNReal)
    {gammaFull Crow : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z))
    (hCrow : 0 ≤ Crow)
    (monitoredPrimes : Finset ℕ)
    (hprime : ∀ p ∈ monitoredPrimes, p.Prime)
    (hleY : ∀ p ∈ monitoredPrimes, p ≤ yNat B.sampleData.n)
    (hmoving : ∀ p ∈ monitoredPrimes,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m ↦ B.vectorFamily.scalarFamily.score m
            (B.vectorFamily.vectorField (B.targetVector Delta)
              (B.effectiveParamEquiv z)))
          (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ)) :
    ∀ p ∈ monitoredPrimes,
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
        |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m ↦ B.vectorFamily.scalarFamily.score m
            (B.vectorFamily.vectorField (B.targetVector Delta)
              (B.effectiveParamEquiv z)))
          (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ) := by
  intro p hp z hz
  by_cases hpW : p ≤ B.sampleData.W
  · have hzero := B.covariance_headPrimeMarkedValuation_vectorField_eq_zero
      hhead (B.effectiveParamEquiv z) Delta hgammaFull
        (hFull z hz) (hprime p hp) hpW
    rw [hzero, abs_zero]
    exact div_nonneg hCrow (by positivity)
  · apply hmoving p hp
      (mem_primeBand.mpr ⟨hprime p hp, Nat.lt_of_not_ge hpW,
        hleY p hp⟩) z hz

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalFeasibilitySlackEventually -/
section


/-!
# Canonical eventual feasibility slack for Proposition 8.7

The finite ODE assembly asks for an exponential feasibility inequality whose
nuisance coefficient is attached to the current canonical bridge data.  The
coefficient is uniformly bounded by the head-cardinality ceiling.  Therefore,
after `W`, the head type, and the effective ball have been fixed, the required
inequality follows from `L(n) -> infinity`; it is not an analytic hypothesis
at the final Proposition 8.7 call site.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Uniform eventual form of the literal feasibility slack used by the
canonical ODE assembly. -/
theorem eventually_canonical_exponential_slack_le_L
    (U : ℝ) (hU : 1 ≤ U) (W : ℕ) (a : NNReal)
    (Cfixed Cactive : ℝ) (hCactive : 0 ≤ Cactive) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Cfixed +
            Real.exp (2 *
              ((PaperStatisticNorm.valuationLogCoefficient
                    U B.sampleData.W +
                  B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
              Cactive ≤ B.L := by
  let Kceiling : ℝ :=
    2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
      nuisanceStatisticCoefficientCeiling Head U) * (3 * (a : ℝ)))
  have hlarge := eventually_fixed_exponential_slack_le_L
    Cfixed Kceiling Cactive
  filter_upwards [hlarge] with n hlargeN
  intro B hBn hBW
  have hcoeff :
      PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U ≤
        PaperStatisticNorm.valuationLogCoefficient U W +
          nuisanceStatisticCoefficientCeiling Head U := by
    rw [hBW]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hscaleNonneg : 0 ≤ 3 * (a : ℝ) := by positivity
  have hexponent :
      2 * ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ))) ≤
        Kceiling := by
    dsimp only [Kceiling]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hscaleNonneg]
  have hexp :
      Real.exp (2 *
          ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) ≤
        Real.exp Kceiling := Real.exp_le_exp.mpr hexponent
  have hscaled := mul_le_mul_of_nonneg_right hexp hCactive
  calc
    Cfixed +
          Real.exp (2 *
            ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
              B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
            Cactive ≤
        Cfixed + Real.exp Kceiling * Cactive :=
      by linarith
    _ ≤ B.L := by
      change Cfixed + Real.exp Kceiling * Cactive ≤
        Scale.L B.sampleData.n
      rw [hBn]
      exact hlargeN

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalEventually -/
section


/-!
# Closed canonical form of paper Proposition 8.7

This theorem composes the exact Lemmas 8.4 and 8.6 terminals with the
canonical target, nuisance-reserve, full-gap, marked-row, speed, and
feasibility packages.  Its public statement is
`CanonicalProposition87Statement`; in particular no analytic estimate is a
call-site premise.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport MovingLowGaugeTransfer
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

set_option maxHeartbeats 4000000 in
/-- Assumption-free paper-order canonical Proposition 8.7. -/
theorem canonical_proposition87
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    CanonicalProposition87Statement cMesh I U Cprom Cbank ledger := by
  unfold CanonicalProposition87Statement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨relTol, hrelTol, Csharp, hCsharp, Cordinary, hCordinary,
      Crow, hCrow, Creg, hCreg, hCregEq,
      _Crel, _hCrel, Wrel, hRel⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
      cMesh hcMesh
  obtain ⟨varTol, hvarTol, gammaSlow, hgammaSlow,
      _Cvar, _hCvar, Wvar, hVar⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
      cMesh Creg hcMesh hCreg
  obtain ⟨Rproj, hRproj, ratioTol, hratioTol, Wratio, hRatio⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_momentRatio
  obtain ⟨Wmarked, hMarkedRoot⟩ :=
    exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
      I U hU hlowerOne hupperU Cprom Cbank ledger
  let meshTol : ℝ := min relTol (min varTol ratioTol)
  let W₀ : ℕ := max 2 (max Wrel (max Wvar (max Wratio Wmarked)))
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hrelTol (lt_min hvarTol hratioTol)
  refine ⟨meshTol, hmeshTol, W₀, ?_⟩
  intro W hW Head _instHeadFintype _instHeadDecidable _instHeadNonempty
    Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hWrel : Wrel ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWvar : Wvar ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWratio : Wratio ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWmarked : Wmarked ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  let K : ℝ := 2 * Real.log 4
  let Tband : ℝ := (1 + Rproj) * Ctarget
  let Ccoef : ℝ := 1 + Creg
  let CL1 : ℝ := 7 + Creg * K
  let A : ℝ := K * Creg * Tband + Ctarget
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hTband : 0 ≤ Tband := by
    dsimp only [Tband]
    positivity
  have hCcoef : 0 ≤ Ccoef := by dsimp only [Ccoef]; positivity
  have hCL1 : 0 ≤ CL1 := by dsimp only [CL1]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨speed, a, hspeedOne, hspeedLeA, _haeq, hSpeed⟩ :=
    exists_speed_radius_with_canonicalTwoStage_bounds_uniformTypes
      (CinvOrd := Cordinary) (Tband := Tband) (Creg := Creg)
      (Tslow := Ctarget) (K := K) (gammaSlow := gammaSlow)
      (Ccoef := Ccoef) hTband hCreg hCtarget hK hgammaSlow hCcoef
  have ha : 0 < (a : ℝ) := by
    have hsa : (speed : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hspeedLeA
    linarith
  obtain ⟨CrowMarked, hCrowMarked, hMarkedMesh⟩ :=
    hMarkedRoot W hWmarked hCordinary.le hTband hA hgammaSlow hCreg
      Phead hHeadLe a marginFloor hmarginFloor
  let Cpost : ℝ := Cinitial + Cmass * CrowMarked
  have hCpost : 0 ≤ Cpost := by
    dsimp only [Cpost]
    positivity
  refine ⟨a, ha, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hfineRel : delta + eta ≤ relTol :=
    hfine.trans (min_le_left relTol (min varTol ratioTol))
  have hfineVar : delta + eta ≤ varTol :=
    hfine.trans ((min_le_right relTol (min varTol ratioTol)).trans
      (min_le_left varTol ratioTol))
  have hfineRatio : delta + eta ≤ ratioTol :=
    hfine.trans ((min_le_right relTol (min varTol ratioTol)).trans
      (min_le_right varTol ratioTol))
  obtain ⟨epsilonRel, _hepsilonRel0, _hepsilonRel,
      _hepsilonRelRate, hRelN⟩ :=
    hRel W hWrel M hdelta hPermitted hfineRel Head Phead hPhead
      I U hU hlowerOne hupperU Cprom Cbank ledger
      a marginFloor hmarginFloor
  have hVarN := hVar W hWvar M hdelta hPermitted hfineVar
    Phead hPhead I U hU hlowerOne hupperU Cprom Cbank ledger
      a marginFloor hmarginFloor
  have hRatioN := hRatio W hWratio M hdelta hfineRatio
    (Head := Head)
  have hMomentN := eventually_bandFirstMoment_le_two_log_four
    (Head := Head) (Band := Fin (M.cellCount + 1)) W
  have hNuisanceN := eventually_canonical_twoStage_nuisance_halfReserves
    (Band := Fin (M.cellCount + 1)) Phead I U hU hlowerOne hupperU
      Cprom Cbank ledger W hWone hHeadLe a marginFloor hmarginFloor
      (CinvOrd := Cordinary) (Tband := Tband) (CL1 := CL1)
      (gammaSlow := gammaSlow) (A := A)
      hCordinary.le hTband hCL1 hgammaSlow hA
  have hMarkedN := hMarkedMesh hdelta M
  have hSlackN := eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Fin (M.cellCount + 1))
      U hU W a Cfixed Cactive hCactive
  filter_upwards [hRelN, hVarN, hRatioN, hMomentN, hNuisanceN,
    hMarkedN, hSlackN] with n hRelAt hVarAt hRatioAt hMomentAt
      hNuisanceAt hMarkedAt hSlackAt
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv monitoredPrimes hprime hleY
    markedTarget N _hN hqMass hinitialMarked Fixed _instFixedFintype
    fixedValue fixedWeight quota hquota hheadSeparated
    hfrozenFeasible hfrozenLedger hactiveLedger
  have hBWlarge : 1 < B.sampleData.W := by
    rw [hBW]
    exact hWone
  have hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W := by
    intro h p
    rw [hcanonical, hBW]
    exact hPhead h p
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiIntervals : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiU : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound U B.sampleData.n := by
    intro sigma
    rw [hhiIntervals]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperU sigma) B.sampleData.n
  have hcompat : B.HasPrimeLogCompatibility :=
    B.hasPrimeLogCompatibility_of_exactHeadPrimes hhead
  have hratio : (∑ j : Fin (M.cellCount + 1),
      B.harmonicMass j * B.bandCenter j) ≤
      Rproj * sharpWeightTotal B.harmonicMass B.bandCenter :=
    hRatioAt B hBn hBW hpartition
  have hmoment : (∑ j : Fin (M.cellCount + 1),
      B.harmonicMass j * B.bandCenter j) ≤ K := by
    simpa only [K] using hMomentAt B hBn hBW
  obtain ⟨hdev, hgeomL1, hVlower, hVupper, hVcenter,
      e, he, hinv, hinvOrd, hBaseZ⟩ :=
    hRelAt B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
      hscale T hTmargin hbaseline
  have hslowRow : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)) j,
      |B.normalizedBandCovarianceRow (B.effectiveParamEquiv z)
        (B.nuisanceResidualScore (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) B.slowScore) j| ≤
        (Crow * B.w) * B.bandCenter j := by
    intro z hz j
    exact (hBaseZ z hz).1 j
  have hreg : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz)) ≤ Creg * B.w := by
    intro z hz
    exact (hBaseZ z hz).2.2.1
  have hcoeff : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ))
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |B.actualCompensatedCoefficient
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz)) p| ≤ Ccoef * B.w := by
    intro z hz p
    simpa only [Ccoef] using (hBaseZ z hz).2.2.2.1 p
  have hcoeffL1 : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      B.partition.compensatedL1
        (B.actualBandRegression (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz)) ≤ CL1 * B.w := by
    intro z hz
    simpa only [CL1, K] using (hBaseZ z hz).2.2.2.2.1
  have hvariance : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      gammaSlow * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance (B.effectiveParamEquiv z)
          (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
          (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
            hlowerOne hupperU hlo hhiIntervals T hbaseline
              hBWlarge z hz) (e z hz) := by
    intro z hz
    exact (hVarAt B hBn hBW hBWlarge hsep hremaining hcanonical
      hpartition hscale T hTmargin hbaseline z hz (e z hz)
      (hreg z hz) hdev hgeomL1 hVlower hVupper hVcenter).1
  have hzero : (0 : B.EffectiveParamSpace) ∈
      closedBall (0 : B.EffectiveParamSpace) (a : ℝ) := by
    simpa only [mem_closedBall, dist_self] using (show (0 : ℝ) ≤ a by
      positivity)
  have htargetPackage : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband ∧
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤ Ctarget ∧
      |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
          hlowerOne hupperU hlo hhiIntervals T hbaseline
            hBWlarge z hz) (e z hz) Delta| ≤
          B.twoStageCompensatedTargetBoundOrdinaryFast
            Creg Tband Ctarget ∧
      B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Ctarget ≤ B.w * A := by
    intro z hz
    simpa only [Tband, A, K] using
      B.canonicalTwoStageTargetPackage_of_envelopes
        (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
          hlowerOne hupperU hlo hhiIntervals T hbaseline
            hBWlarge z hz) (e z hz) Delta hCtarget hRproj.le hCreg
          henv hratio hmoment (hreg z hz)
  have htargetBand := (htargetPackage 0 hzero).1
  have htargetSlow := (htargetPackage 0 hzero).2.1
  have htargetComp : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
          hlowerOne hupperU hlo hhiIntervals T hbaseline
            hBWlarge z hz) (e z hz) Delta| ≤ B.w * A := by
    intro z hz
    exact (htargetPackage z hz).2.2.1.trans
      (htargetPackage z hz).2.2.2
  have hNuisanceRows : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.bandRegressionScore
          ((e z hz).symm (B.projectedNormalizedTargetBand Delta)))‖ ≤
          B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
            (1 / 2) ∧
      ‖B.nuisanceCovarianceVector (B.effectiveParamEquiv z)
        (B.postBandPrimeScore
          (B.actualBandRegression (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhiIntervals T hbaseline
                hBWlarge z hz) (e z hz)))‖ ≤
          B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
            (gammaSlow * B.w / (2 * (1 + A))) := by
    intro z hz
    exact hNuisanceAt B hBn hBW hBWlarge hsep hremaining hcanonical
      T hTmargin hbaseline z hz (e z hz) Delta (hinvOrd z hz)
        htargetBand (hcoeffL1 z hz)
  let gammaN : ℝ :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let gammaFull : ℝ :=
    B.canonicalTwoStageFullGap Csharp gammaSlow Creg gammaN
  have hGamma : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      gammaN * ‖v‖ ^ 2 ≤ inner ℝ v
        (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
    intro z hz v
    simpa only [gammaN] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhiIntervals T hbaseline
          hBWlarge z hz v
  have hFullAt : ∀ z (hz : z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ)),
      0 < gammaFull ∧ B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z) := by
    intro z hz
    simpa only [gammaN, gammaFull] using
      B.hasCovarianceGap_of_sameMap_sharpInverse_and_slow
        (B.effectiveParamEquiv z)
        (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
        (by intro v; simpa only [gammaN] using hGamma z hz v)
        (e z hz) (he z hz) hCsharp hgammaSlow hCreg
          (hinv z hz) (hvariance z hz) (hreg z hz)
  have hgammaFull : 0 < gammaFull := (hFullAt 0 hzero).1
  have hFull : ∀ z ∈ closedBall
      (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gammaFull
        (B.effectiveParamEquiv z) := by
    intro z hz
    exact (hFullAt z hz).2
  let movingPrimes := monitoredPrimes.filter
    (fun p ↦ p ∈ primeBand B.sampleData.n B.sampleData.W)
  have hMovingFiltered := hMarkedAt B hBn hBW hBWlarge hsep hremaining
    hcanonical hpartition hscale Delta T hTmargin hbaseline
      hgammaFull hFull e he hvariance htargetComp hinvOrd htargetBand hreg
      movingPrimes (by
        intro p hp
        exact (Finset.mem_filter.mp hp).2)
  have hMoving : ∀ p ∈ monitoredPrimes,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta)
            (B.effectiveParamEquiv z)))
        (B.effectiveParamEquiv z)| ≤ CrowMarked / (p : ℝ) := by
    intro p hp hband z hz
    exact hMovingFiltered p (Finset.mem_filter.mpr ⟨hp, hband⟩) z hz
  have hMarkedAll := B.uniform_allPrime_markedRow_of_exactHead_and_moving
    hhead Delta a hgammaFull hFull hCrowMarked monitoredPrimes
      hprime hleY hMoving
  obtain ⟨hspeedPrime, hspeedNuisance, hspeedSlow⟩ := hSpeed B hmoment
  have hlarge := hSlackAt B hBn hBW
  have hfit :=
    B.exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
      I hU hlowerOne hupperU hlo hhiIntervals T hbaseline hBWlarge
      hcompat hhead Delta a speed hCsharp hCordinary.le hgammaSlow
      hCrow hTband hCtarget
      (mul_nonneg hCcoef B.w_pos.le)
      e he hinv hinvOrd hvariance hslowRow htargetBand htargetSlow
      hcoeff (fun z hz ↦ (hNuisanceRows z hz).1)
      (fun z hz ↦ (hNuisanceRows z hz).2)
      (by simpa only [hCregEq] using hspeedPrime)
      (by simpa only [A, hCregEq] using hspeedNuisance)
      (by simpa only [hCregEq] using hspeedSlow) hspeedLeA
      monitoredPrimes CrowMarked hCrowMarked hMarkedAll markedTarget
      N Cinitial Cmass
      (by
        intro p hp
        exact_mod_cast (hprime p hp).pos)
      hqMass hinitialMarked fixedValue fixedWeight quota hquota
      hU hhiU hheadSeparated hfrozenFeasible hfrozenLedger
      hactiveLedger hlarge
  simpa only [HasPhysicallyCenteredFixedPartitionFit, Cpost] using hfit

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal001_009.{u_1, u_2} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.canonical_proposition87
