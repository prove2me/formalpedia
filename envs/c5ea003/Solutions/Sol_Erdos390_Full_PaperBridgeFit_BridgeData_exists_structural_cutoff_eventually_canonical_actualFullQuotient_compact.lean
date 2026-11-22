-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_structural_cutoff_eventually_canonical_actualFullQuotient_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:16:27.279855+00:00
-- url     : https://prove2.me/submissions/14adf284-ed50-43a4-a794-0668826b771e

import Definitions.Def_erdos390_remaining_analytic_propositions_003
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
import Theorems.Thm_Erdos390_Full_FiniteSignedQuadraticEntryTransfer_abs_matrixQuadratic_sub_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_actualWeightedRow_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_nuisanceRegressionLoss_primeValuationScore_le_of_marked
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_firstMomentWeightedAbelRemainder_le
import Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_primeRowResidual_le_of_relative_quadrature
import Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually
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

/- Source module: Erdos390.Lemma84 -/
section


/-!
# The finite-dimensional core of Lemma 8.4

This file formalizes only the algebraic part of the moving-low-cell
arithmetic quotient argument.  The Poisson--Dickman gap, prime
quadrature, and marked covariance estimates occur below as fields of an
explicit input structure.  Thus this file contains no postulate claiming
those analytic results.
-/

namespace Erdos390.Lemma84

open scoped BigOperators

noncomputable section

section WeightedBands

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]



namespace WeightedBandData

variable (d : WeightedBandData Prime Band)







































theorem primeInner_add_left (x y z : Prime → ℝ) :
    d.primeInner (fun p => x p + y p) z =
      d.primeInner x z + d.primeInner y z := by
  unfold primeInner
  calc
    (∑ p, d.weight p * (x p + y p) * z p) =
        ∑ p, (d.weight p * x p * z p + d.weight p * y p * z p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := Finset.sum_add_distrib

theorem primeInner_add_right (x y z : Prime → ℝ) :
    d.primeInner x (fun p => y p + z p) =
      d.primeInner x y + d.primeInner x z := by
  unfold primeInner
  calc
    (∑ p, d.weight p * x p * (y p + z p)) =
        ∑ p, (d.weight p * x p * y p + d.weight p * x p * z p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := Finset.sum_add_distrib

theorem primeInner_smul_left (a : ℝ) (x y : Prime → ℝ) :
    d.primeInner (fun p => a * x p) y = a * d.primeInner x y := by
  unfold primeInner
  calc
    (∑ p, d.weight p * (a * x p) * y p) =
        ∑ p, a * (d.weight p * x p * y p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm

theorem primeInner_smul_right (a : ℝ) (x y : Prime → ℝ) :
    d.primeInner x (fun p => a * y p) = a * d.primeInner x y := by
  unfold primeInner
  calc
    (∑ p, d.weight p * x p * (a * y p)) =
        ∑ p, a * (d.weight p * x p * y p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm

theorem primeInner_comm (x y : Prime → ℝ) :
    d.primeInner x y = d.primeInner y x := by
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem primeNormSq_add (x y : Prime → ℝ) :
    d.primeNormSq (fun p => x p + y p) =
      d.primeNormSq x + d.primeNormSq y + 2 * d.primeInner x y := by
  unfold primeNormSq
  rw [d.primeInner_add_left, d.primeInner_add_right,
    d.primeInner_add_right, d.primeInner_comm y x]
  ring

theorem primeNormSq_smul (a : ℝ) (x : Prime → ℝ) :
    d.primeNormSq (fun p => a * x p) = a ^ 2 * d.primeNormSq x := by
  unfold primeNormSq
  rw [d.primeInner_smul_left, d.primeInner_smul_right]
  ring

theorem primeNormSq_nonneg (x : Prime → ℝ) : 0 ≤ d.primeNormSq x := by
  unfold primeNormSq primeInner
  apply Finset.sum_nonneg
  intro p hp
  have hw : 0 ≤ d.weight p := le_of_lt (d.weight_pos p)
  nlinarith [sq_nonneg (x p)]

theorem bandNormSq_nonneg (x : Band → ℝ) : 0 ≤ d.bandNormSq x := by
  unfold bandNormSq bandInner
  apply Finset.sum_nonneg
  intro j hj
  have hH : 0 ≤ d.mass j := by
    unfold mass
    apply Finset.sum_nonneg
    intro p hp
    exact le_of_lt (d.weight_pos p)
  nlinarith [sq_nonneg (x j)]

/-- A symmetric normalized prime-row bound controls the whole quadratic
error.  With `weight p = 1 / p`, its hypothesis is exactly
`sup_p p * sum_r |E p r| ≤ ε`. -/
theorem symmetric_prime_row_quadratic_error
    (E : Prime → Prime → ℝ) (c : Prime → ℝ) (eps : ℝ)
    (hsymm : ∀ p r, E p r = E r p)
    (hrow : ∀ p, (∑ r, |E p r|) ≤ eps * d.weight p) :
    |primeQuadratic E c| ≤ eps * d.primeNormSq c := by
  let Sabs : ℝ := ∑ p, ∑ r, |E p r * c p * c r|
  let Srow : ℝ := ∑ p, c p ^ 2 * (∑ r, |E p r|)
  have htriangle : |primeQuadratic E c| ≤ Sabs := by
    unfold primeQuadratic Sabs
    calc
      |∑ p, ∑ r, E p r * c p * c r| ≤
          ∑ p, |∑ r, E p r * c p * c r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p, ∑ r, |E p r * c p * c r| := by
        apply Finset.sum_le_sum
        intro p hp
        exact Finset.abs_sum_le_sum_abs _ _
  have hpair (p r : Prime) :
      2 * |E p r * c p * c r| ≤
        |E p r| * (c p ^ 2 + c r ^ 2) := by
    have hab : 2 * |c p| * |c r| ≤ |c p| ^ 2 + |c r| ^ 2 := by
      nlinarith [sq_nonneg (|c p| - |c r|)]
    calc
      2 * |E p r * c p * c r| =
          |E p r| * (2 * |c p| * |c r|) := by
            simp only [abs_mul]
            ring
      _ ≤ |E p r| * (|c p| ^ 2 + |c r| ^ 2) :=
        mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = |E p r| * (c p ^ 2 + c r ^ 2) := by
        rw [sq_abs, sq_abs]
  have hpairSum :
      2 * Sabs ≤ ∑ p, ∑ r, |E p r| * (c p ^ 2 + c r ^ 2) := by
    unfold Sabs
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    exact hpair p r
  have hsymSum :
      (∑ p, ∑ r, |E p r| * (c p ^ 2 + c r ^ 2)) = 2 * Srow := by
    have hfirst :
        (∑ p, ∑ r, |E p r| * c p ^ 2) = Srow := by
      unfold Srow
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have hsecond :
        (∑ p, ∑ r, |E p r| * c r ^ 2) = Srow := by
      rw [Finset.sum_comm]
      unfold Srow
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hsymm r p]
      ring
    calc
      (∑ p, ∑ r, |E p r| * (c p ^ 2 + c r ^ 2)) =
          (∑ p, ∑ r, |E p r| * c p ^ 2) +
            (∑ p, ∑ r, |E p r| * c r ^ 2) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
      _ = 2 * Srow := by rw [hfirst, hsecond]; ring
  have hrowSum : Srow ≤ eps * d.primeNormSq c := by
    unfold Srow primeNormSq primeInner
    calc
      (∑ p, c p ^ 2 * ∑ r, |E p r|) ≤
          ∑ p, c p ^ 2 * (eps * d.weight p) := by
            apply Finset.sum_le_sum
            intro p hp
            exact mul_le_mul_of_nonneg_left (hrow p) (sq_nonneg _)
      _ = eps * ∑ p, d.weight p * c p * c p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  rw [hsymSum] at hpairSum
  nlinarith





theorem mass_ne_zero (j : Band) : d.mass j ≠ 0 :=
  ne_of_gt (d.mass_pos j)

/-- The definition of the arithmetic band center gives exact weighted
centering on each fiber. -/
theorem center_fiber_sum (j : Band) :
    ∑ p ∈ d.fiber j, d.weight p * (d.center j - d.coord p) = 0 := by
  let H : ℝ := d.mass j
  let N : ℝ := ∑ p ∈ d.fiber j, d.weight p * d.coord p
  have hH : H ≠ 0 := by
    exact d.mass_ne_zero j
  change ∑ p ∈ d.fiber j, d.weight p * (N / H - d.coord p) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hleft :
      (∑ p ∈ d.fiber j, d.weight p * (N / H)) = H * (N / H) := by
    rw [← Finset.sum_mul]
    rfl
  rw [hleft]
  change H * (N / H) - N = 0
  field_simp
  ring

/-- Cellwise centering annihilates every coefficient which is constant
on each band. -/
theorem centered_against_lift (r : Band → ℝ) :
    d.primeInner (d.lift r) d.cellDeviation = 0 := by
  unfold primeInner
  rw [← Finset.sum_fiberwise Finset.univ d.band
    (fun p => d.weight p * d.lift r p * d.cellDeviation p)]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    (∑ p ∈ Finset.univ with d.band p = j,
        d.weight p * d.lift r p * d.cellDeviation p) =
        r j * (∑ p ∈ d.fiber j,
          d.weight p * (d.center j - d.coord p)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr
          · rfl
          · intro p hp
            have hpj : d.band p = j := (Finset.mem_filter.mp hp).2
            simp only [lift, cellDeviation, hpj]
            ring
    _ = 0 := by rw [d.center_fiber_sum j, mul_zero]

theorem primeInner_lifts (x y : Band → ℝ) :
    d.primeInner (d.lift x) (d.lift y) = d.bandInner x y := by
  unfold primeInner bandInner
  rw [← Finset.sum_fiberwise Finset.univ d.band
    (fun p => d.weight p * d.lift x p * d.lift y p)]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ p ∈ Finset.univ with d.band p = j,
        d.weight p * d.lift x p * d.lift y p) =
        ∑ p ∈ d.fiber j, d.weight p * x j * y j := by
          apply Finset.sum_congr
          · rfl
          · intro p hp
            have hpj : d.band p = j := (Finset.mem_filter.mp hp).2
            simp only [lift, hpj]
    _ = (∑ p ∈ d.fiber j, d.weight p) * x j * y j := by
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
    _ = d.mass j * x j * y j := rfl

theorem bandInner_comm (x y : Band → ℝ) :
    d.bandInner x y = d.bandInner y x := by
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bandInner_add_right (x y z : Band → ℝ) :
    d.bandInner x (fun j => y j + z j) =
      d.bandInner x y + d.bandInner x z := by
  unfold bandInner
  calc
    (∑ j, d.mass j * x j * (y j + z j)) =
        ∑ j, (d.mass j * x j * y j + d.mass j * x j * z j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := Finset.sum_add_distrib

theorem bandInner_smul_right (a : ℝ) (x y : Band → ℝ) :
    d.bandInner x (fun j => a * y j) = a * d.bandInner x y := by
  unfold bandInner
  calc
    (∑ j, d.mass j * x j * (a * y j)) =
        ∑ j, a * (d.mass j * x j * y j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm





theorem coord_decomposition (p : Prime) :
    d.coord p = d.lift d.center p - d.cellDeviation p := by
  simp [lift, cellDeviation]

theorem coordEnergy_eq :
    d.coordEnergy = d.centerEnergy + d.cellVariance := by
  let a : Prime → ℝ := d.lift d.center
  let g : Prime → ℝ := d.cellDeviation
  have hcoord : d.coord = fun p => a p + (-1 : ℝ) * g p := by
    funext p
    rw [d.coord_decomposition p]
    change a p - g p = a p + (-1 : ℝ) * g p
    ring
  have hag : d.primeInner a g = 0 := by
    simpa [a, g] using d.centered_against_lift d.center
  have haa : d.primeNormSq a = d.centerEnergy := by
    simpa [a, primeNormSq, centerEnergy, bandNormSq] using
      d.primeInner_lifts d.center d.center
  calc
    d.coordEnergy = d.primeNormSq (fun p => a p + (-1 : ℝ) * g p) := by
      rw [show d.coordEnergy = d.primeNormSq d.coord by rfl, hcoord]
    _ = d.primeNormSq a + d.primeNormSq (fun p => (-1 : ℝ) * g p) +
          2 * d.primeInner a (fun p => (-1 : ℝ) * g p) :=
      d.primeNormSq_add a (fun p => (-1 : ℝ) * g p)
    _ = d.centerEnergy + d.cellVariance := by
      rw [d.primeNormSq_smul, d.primeInner_smul_right, haa, hag]
      simp [g, cellVariance]

theorem physicalSq_expansion (q : Band → ℝ) (lambda mu : ℝ)
    (hq : d.inGauge q) :
    d.physicalSq (fun j => q j + lambda * d.center j) mu =
      d.bandNormSq q + (lambda - mu) ^ 2 * d.centerEnergy +
        mu ^ 2 * d.cellVariance := by
  let x : Prime → ℝ := d.lift q
  let a : Prime → ℝ := d.lift d.center
  let g : Prime → ℝ := d.cellDeviation
  let y : Prime → ℝ := fun p => (lambda - mu) * a p
  let z : Prime → ℝ := fun p => mu * g p
  have hres :
      d.residual (fun j => q j + lambda * d.center j) mu =
        fun p => (x p + y p) + z p := by
    funext p
    unfold residual lift
    rw [show d.coord p = a p - g p by
      simpa [a, g] using d.coord_decomposition p]
    simp only [x, a, y, z, g, lift]
    ring
  have hxx : d.primeNormSq x = d.bandNormSq q := by
    simpa [x, primeNormSq, bandNormSq] using d.primeInner_lifts q q
  have haa : d.primeNormSq a = d.centerEnergy := by
    simpa [a, primeNormSq, centerEnergy, bandNormSq] using
      d.primeInner_lifts d.center d.center
  have hgg : d.primeNormSq g = d.cellVariance := rfl
  have hxa : d.primeInner x a = 0 := by
    calc
      d.primeInner x a = d.bandInner q d.center := by
        simpa [x, a] using d.primeInner_lifts q d.center
      _ = d.bandInner d.center q := d.bandInner_comm q d.center
      _ = 0 := hq
  have hxg : d.primeInner x g = 0 := by
    simpa [x, g] using d.centered_against_lift q
  have hag : d.primeInner a g = 0 := by
    simpa [a, g] using d.centered_against_lift d.center
  unfold physicalSq
  rw [hres, d.primeNormSq_add, d.primeNormSq_add,
    d.primeInner_add_left]
  dsimp only [y, z]
  rw [d.primeNormSq_smul, d.primeNormSq_smul,
    d.primeInner_smul_right, d.primeInner_smul_right,
    d.primeInner_smul_left, d.primeInner_smul_right,
    hxx, haa, hgg, hxa, hxg, hag]
  ring

theorem physicalMinimizer_normal (b : Band → ℝ)
    (hcoord : d.coordEnergy ≠ 0) :
    d.primeInner d.coord (d.residual b (d.physicalMinimizer b)) = 0 := by
  have hres : d.residual b (d.physicalMinimizer b) =
      fun p => d.lift b p +
        (-d.physicalMinimizer b) * d.coord p := by
    funext p
    simp only [residual]
    ring
  rw [hres, d.primeInner_add_right, d.primeInner_smul_right]
  have hE : d.primeInner d.coord d.coord ≠ 0 := by
    simpa [coordEnergy, primeNormSq] using hcoord
  unfold physicalMinimizer coordEnergy primeNormSq
  field_simp [hE]
  ring



theorem physical_lower_bound (q : Band → ℝ) (lambda : ℝ)
    (hq : d.inGauge q) (hV : 0 ≤ d.cellVariance) :
    d.bandNormSq q ≤
      d.physicalSq (fun j => q j + lambda * d.center j)
        (d.physicalMinimizer (fun j => q j + lambda * d.center j)) := by
  rw [d.physicalSq_expansion q lambda _ hq]
  have hA : 0 ≤ d.centerEnergy := d.bandNormSq_nonneg d.center
  have hfirst :
      0 ≤ (lambda - d.physicalMinimizer
        (fun j => q j + lambda * d.center j)) ^ 2 * d.centerEnergy :=
    mul_nonneg (sq_nonneg _) hA
  have hsecond :
      0 ≤ d.physicalMinimizer
        (fun j => q j + lambda * d.center j) ^ 2 * d.cellVariance :=
    mul_nonneg (sq_nonneg _) hV
  linarith

theorem gaugePart_inGauge (b : Band → ℝ) (hA : d.centerEnergy ≠ 0) :
    d.inGauge (d.gaugePart b) := by
  have hE : d.bandInner d.center d.center ≠ 0 := by
    simpa [centerEnergy, bandNormSq] using hA
  have hfun : d.gaugePart b = fun j =>
      b j + (-d.gaugeCoefficient b) * d.center j := by
    funext j
    simp only [gaugePart]
    ring
  unfold inGauge
  rw [hfun, d.bandInner_add_right, d.bandInner_smul_right]
  unfold gaugeCoefficient centerEnergy bandNormSq
  field_simp [hE]
  ring

theorem gauge_decomposition (b : Band → ℝ) (j : Band) :
    d.gaugePart b j + d.gaugeCoefficient b * d.center j = b j := by
  simp only [gaugePart]
  ring





/-!
## Conditional bridge

The next structure is the exact boundary between the finite argument and
the presently external analytic work.  Its fields are a leading
Poisson--Dickman/quadrature form, an actual marked covariance form, the
nuisance loss, and quantitative comparisons between them.  No field is
the desired quotient conclusion.
-/













end WeightedBandData

end WeightedBands

end

end Erdos390.Lemma84

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

/- Source module: Erdos390.Full.ConditionedPoissonLimit -/
section


/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/













































































lemma covarianceKernel_comm (s t : ℝ) :
    covarianceKernel s t = covarianceKernel t s := by
  unfold covarianceKernel
  rw [add_comm]
  ring

















/-! ## Density-weighted Palm moments and covariance -/



lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/

















































/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

end

/- Source module: Erdos390.Full.PoissonDickmanKernelBounds -/
section


/-!
# Uniform bounds for the removable Poisson--Dickman kernel

The moving-low-cell transfer needs a bound which remains valid as either
prime coordinate approaches zero.  The continuous quotient constructed in
`ConditionedPoissonLimit` gives such a bound on the compact unit square.  This
file exports the compactness consequence and converts it back to literal
bounds for the covariance kernel.  No conditioned-law or Palm identity is
used here.
-/

open Set

noncomputable section

namespace Erdos390.Full.PoissonDickmanKernelBounds

open ConditionedPoissonLimit

/-- The removable quotient `K(s,t)/t` is uniformly bounded on the closed unit
square. -/
theorem exists_covarianceKernelQuotient_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernelQuotient s t| ≤ C := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn
    continuous_uncurry_covarianceKernelQuotient.continuousOn
  have hzeroMem : ((0 : ℝ), (0 : ℝ)) ∈ S := by
    exact ⟨by norm_num, by norm_num⟩
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (covarianceKernelQuotient 0 0)).trans
      (hC (0, 0) hzeroMem)
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht
  simpa only [Real.norm_eq_abs] using hC (s, t) ⟨hs, ht⟩

/-- Consequently the original kernel vanishes at least linearly in its
second coordinate, uniformly in the first. -/
theorem exists_covarianceKernel_abs_le_second :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * t := by
  obtain ⟨C, hCnonneg, hC⟩ := exists_covarianceKernelQuotient_bound
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht
  rw [← mul_covarianceKernelQuotient_eq_kernel hs ht, abs_mul,
    abs_of_nonneg ht.1]
  calc
    t * |covarianceKernelQuotient s t| ≤ t * C :=
      mul_le_mul_of_nonneg_left (hC s hs t ht) ht.1
    _ = C * t := by ring



end Erdos390.Full.PoissonDickmanKernelBounds

end

/- Source module: Erdos390.Full.KernelPrimeQuadrature -/
section


/-!
# Weighted prime quadrature for the Poisson--Dickman kernel

This file generalizes the scalar Abel summation used for `H_j` to a smooth
test function on logarithmic prime coordinates.  The first layer is an exact
finite identity for the actual primes; later declarations specialize it to
the Poisson--Dickman covariance kernel and its compact derivative bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.KernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit





lemma continuous_covarianceKernelDerivativeSecondExtension_left (s : ℝ) :
    Continuous (covarianceKernelDerivativeSecondExtension s) := by
  unfold covarianceKernelDerivativeSecondExtension
  exact (continuous_derivFExtension.comp
      (continuous_const.add continuous_id)).sub
    (continuous_const.mul continuous_derivFExtension)





lemma covarianceKernelDerivativeSecondExtension_eq {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelDerivativeSecondExtension s t =
      covarianceKernelDerivativeSecond s t := by
  have hst : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  unfold covarianceKernelDerivativeSecondExtension
  unfold covarianceKernelDerivativeSecond
  rw [derivFExtension_eq_deriv_of_mem hst,
    derivFExtension_eq_deriv_of_mem
      ⟨ht.1, ht.2.trans (by norm_num)⟩]

lemma continuous_covarianceKernel_left (s : ℝ) :
    Continuous (covarianceKernel s) := by
  exact continuous_covarianceKernel.comp
    (continuous_const.prodMk continuous_id)

lemma hasDerivAt_covarianceKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (covarianceKernel s)
      (covarianceKernelDerivativeSecond s t) t := by
  have ht₂ : t ∈ Icc (0 : ℝ) 2 :=
    ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hst₂ : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hshift : HasDerivAt (fun u : ℝ => s + u) 1 t := by
    simpa only [zero_add] using
      (hasDerivAt_const t s).add (hasDerivAt_id t)
  have hfirst := (differentiableAt_F hst₂).hasDerivAt.comp t hshift
  have hsecond := (differentiableAt_F ht₂).hasDerivAt.const_mul (F s)
  convert hfirst.sub hsecond using 1
  unfold covarianceKernelDerivativeSecond
  ring



lemma realLogCoordinate_mem_unit {z x : ℝ}
    (hz : 1 < z) (hx : 1 ≤ x) (hxz : x ≤ z) :
    realLogCoordinate z x ∈ Icc (0 : ℝ) 1 := by
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxnonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log (zero_lt_one.trans_le hx) hxz
  unfold realLogCoordinate
  constructor
  · exact div_nonneg hlogxnonneg hlogzpos.le
  · exact (div_le_one hlogzpos).2 hlogxz





































































end Erdos390.Full.KernelPrimeQuadrature

end

/- Source module: Erdos390.Full.PoissonDickmanDirichlet -/
section


/-!
# A Dirichlet-form route for the Poisson--Dickman covariance kernel

This file isolates the deterministic part of the proposed kernel argument.
For a test function written as `f(t) = t * q(t)`, the covariance quadratic
form is exactly a symmetric Dirichlet energy.  The identity uses only the
Dickman averaging equation already proved in `ConditionedPoissonLimit`; it
does not use a conditional probability measure on the zero-probability
fibre.

The file also closes the sign of the Dirichlet kernel from the delay equation.
It formalizes the classical first-failure proof that the negative logarithmic
derivative of the Dickman function is strictly increasing on the required
range, turns this into the four-point log-concavity inequality, and hence
proves strict negativity of the covariance kernel in the open square.
-/

open Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.PoissonDickmanDirichlet

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit

/-! ## Dickman log-concavity from a first-failure argument -/









































private lemma slopeIntegral_shift_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) ≤
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t ≤ U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hmono : ∀ x ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x hx
    · exact hxsmem x hx
    · linarith [hs.1]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcont₁.intervalIntegrable_of_Icc hab)
    (hcont₂.intervalIntegrable_of_Icc hab) hmono
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  ring



lemma log_rho_four_point_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) ≤
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := slopeIntegral_shift_le hs ht
  linarith



lemma rho_four_point_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    rho (U - s - t) * rho U ≤ rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := rho_U_pos
  have hc : 0 < rho (U - s) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_le_exp.mpr (log_rho_four_point_le hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h



/-- The covariance defect is nonpositive on the closed physical square.
This is now an unconditional theorem, obtained from the proved Dickman
log-concavity rather than supplied as an analytic premise. -/
theorem covarianceKernel_nonpos {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernel s t ≤ 0 := by
  have hprod := rho_four_point_le hs ht
  have hU : 0 < rho U := rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_le_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_nonpos.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ ≤ (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]





































































/-! ## Unconditional covariance consequences -/















end Erdos390.Full.PoissonDickmanDirichlet

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

































variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper











end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

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







/-- Exact Schur-variance identity.  This is an equality at finite `n`; the
subsequent continuum and prime-power arguments only estimate its two terms. -/
theorem nuisanceResidualScore_variance_identity [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap F)
        (B.nuisanceResidualScore xi hgamma hgap F) =
      (B.tiltedLaw xi).covariance F F -
        inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
          (B.nuisanceCovarianceVector xi F) := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Zscore : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  have horth := B.nuisanceResidualScore_covariance_zero
    xi hgamma hgap F a
  have hcomm : (B.tiltedLaw xi).covariance
      (B.nuisanceResidualScore xi hgamma hgap F) Zscore = 0 := by
    simpa only [Zscore] using
      ((B.tiltedLaw xi).covariance_comm
        (B.nuisanceResidualScore xi hgamma hgap F) Zscore).trans horth
  have hF : F = fun m ↦
      B.nuisanceResidualScore xi hgamma hgap F m + Zscore m := by
    funext m
    unfold nuisanceResidualScore
    simp only [a, Zscore]
    ring
  have hvarZ := B.inner_nuisanceCovarianceOperator_bilinear xi a a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ a v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ a (B.nuisanceCovarianceOperator xi a) =
    inner ℝ a (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hvarZ] at hsolve
  rw [show (B.tiltedLaw xi).covariance F F =
      (B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m + Zscore m)
        (fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m + Zscore m) by
    rw [← hF] ]
  rw [FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_add_right]
  rw [horth, hcomm, zero_add, add_zero]
  linarith















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

/- Source module: Erdos390.Full.PaperNuisancePrimeLogRows -/
section


/-!
# Exact logarithmic decomposition of the nuisance rows

The physical nuisance coordinate is not an unrelated marked statistic.  The
finite factorization identity in `BridgeData.HasPrimeLogCompatibility`
expresses the medium-prime logarithmic score as a nonzero multiple of the
physical logarithm plus a function of the fixed head tag.  This file solves
that identity for the physical score and does so inside an arbitrary nuisance
linear functional.

The resulting covariance-row identity is exact at finite `n`.  It is the
algebraic attachment used in Lemma 8.6 before applying the analytic estimates
for the prime-log null row and for cell-constant head rows.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



private theorem sum_nuisanceCoord {I : Type*} [Fintype I]
    (f : NuisanceCoord I → ℝ) :
    (∑ z : NuisanceCoord I, f z) =
      f .physical + ∑ h : I, f (.head h) := by
  calc
    (∑ z : NuisanceCoord I, f z) =
        ∑ s : Unit ⊕ I, f ((nuisanceCoordEquiv_PaperNuisancePrimeLogRows I).symm s) := by
      exact Fintype.sum_equiv (nuisanceCoordEquiv_PaperNuisancePrimeLogRows I) f
        (fun s ↦ f ((nuisanceCoordEquiv_PaperNuisancePrimeLogRows I).symm s)) (fun z ↦ by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [nuisanceCoordEquiv_PaperNuisancePrimeLogRows]



/-- An arbitrary nuisance linear functional is exactly its physical
coefficient times `R`, plus a function of the tagged head pattern. -/
theorem inner_nuisanceStatistic_eq_physical_add_headFunction
    [Nonempty Head]
    (z : B.NuisanceSpace) (m : B.sampleData.Sample) :
    inner ℝ z (B.nuisanceStatistic m) =
      z NuisanceCoord.physical * B.physicalScore m +
        B.headFunctionScore (B.nuisanceHeadFunction z) m := by
  rw [PiLp.inner_apply, sum_nuisanceCoord]
  simp only [B.nuisanceStatistic_physical, B.nuisanceStatistic_head,
    RCLike.inner_apply, conj_trivial]
  unfold nuisanceHeadFunction headFunctionScore centeredHeadScore headIndicator
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro h hh
    ring









/-- The compatibility identity with its actual coefficient displayed.  This
avoids selecting an arbitrary witness of `HasPrimeLogCompatibility`. -/
theorem primeLogScore_eq_explicit_physical_add_head
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (m : B.sampleData.Sample) :
    B.primeLogScore m =
      (1 / Real.log (ArithmeticModel.y B.sampleData.n)) *
          B.physicalScore m +
        B.headFunctionScore B.exactPrimeLogHeadFunction m := by
  let logY : ℝ := Real.log (ArithmeticModel.y B.sampleData.n)
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
  unfold physicalScore headFunctionScore exactPrimeLogHeadFunction
  rw [Real.log_div hvalue hn]
  dsimp only [logY] at hlogY
  field_simp [hlogY]
  ring





























end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteAnchoredDirichletQuadratic -/
section


/-!
# Finite anchored Dirichlet quadratic forms

This file records the exact finite algebra needed in the slow-direction
part of paper Lemma 8.6.  A symmetric reference covariance is a graph
Dirichlet energy plus its (possibly nonzero) discrete row-sum residual.
A positive block of anchor vertices then controls the quotient distance to
the constant direction.  The statements are entirely finite; in
particular, no continuum limit or spectral-gap hypothesis is hidden in the
algebra.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteAnchoredDirichletQuadratic

variable {ι : Type*} [Fintype ι]







/-- Exact finite Dirichlet decomposition.  This is the discrete identity
behind the passage from the squarefree reference covariance to the
quotient energy. -/
theorem referenceQuadratic_eq_dirichletEnergy_add_rowResidual
    (weight diagonal : ι → ℝ) (kernel : ι → ι → ℝ) (x : ι → ℝ)
    (hsymm : ∀ i j, kernel i j = kernel j i) :
    referenceQuadratic weight diagonal kernel x =
      dirichletEnergy weight kernel x +
        ∑ i, weight i * rowResidual weight diagonal kernel i * x i ^ 2 := by
  classical
  let D : ℝ := ∑ i, weight i * diagonal i * x i ^ 2
  let L : ℝ := ∑ i, ∑ j,
    weight i * weight j * kernel i j * x i ^ 2
  let R : ℝ := ∑ i, ∑ j,
    weight i * weight j * kernel i j * x j ^ 2
  let C : ℝ := ∑ i, ∑ j,
    weight i * weight j * kernel i j * x i * x j
  have hR : R = L := by
    calc
      R = ∑ i, ∑ j,
          weight j * weight i * kernel j i * x i ^ 2 := by
            dsimp only [R]
            rw [Finset.sum_comm]
      _ = L := by
        dsimp only [L]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsymm j i]
        ring
  have hCtwo :
      (∑ i, ∑ j,
        2 * (weight i * weight j * kernel i j * x i * x j)) = 2 * C := by
    dsimp only [C]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have henergy :
      dirichletEnergy weight kernel x =
        (-L + 2 * C - R) / 2 := by
    unfold dirichletEnergy
    rw [show (∑ i, ∑ j,
        weight i * weight j * (-kernel i j) * (x i - x j) ^ 2) =
          -L + 2 * C - R by
      dsimp only [L, C, R]
      simp_rw [show ∀ i j, weight i * weight j * (-kernel i j) *
          (x i - x j) ^ 2 =
            -(weight i * weight j * kernel i j * x i ^ 2) +
              2 * (weight i * weight j * kernel i j * x i * x j) -
              weight i * weight j * kernel i j * x j ^ 2 by
        intro i j
        ring]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      rw [hCtwo] ]
    ring
  have hresidual :
      (∑ i, weight i * rowResidual weight diagonal kernel i * x i ^ 2) =
        D + L := by
    unfold rowResidual
    calc
      (∑ i, weight i *
          (diagonal i + ∑ j, weight j * kernel i j) * x i ^ 2) =
          (∑ i, weight i * diagonal i * x i ^ 2) +
            ∑ i, weight i * (∑ j, weight j * kernel i j) * x i ^ 2 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = D + L := by
        apply congrArg₂ (fun a b : ℝ => a + b)
        · rfl
        · dsimp only [L]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
  unfold referenceQuadratic
  change D + C = _
  rw [henergy, hresidual, hR]
  ring







/-- The weighted anchor mean gives an exact one-sided Poincare inequality.
The centering equation is stated explicitly so that applications may use a
literal finite arithmetic mean. -/
theorem anchorMass_mul_weightedDistance_le_anchorPairVariation
    (metricWeight anchorWeight : ι → ℝ) (anchor : Finset ι)
    (x : ι → ℝ) (mu : ℝ)
    (hmetric : ∀ i, 0 ≤ metricWeight i)
    (hanchor : ∀ j ∈ anchor, 0 ≤ anchorWeight j)
    (hcenter : ∑ j ∈ anchor, anchorWeight j * (x j - mu) = 0) :
    anchorMass anchorWeight anchor * weightedDistance metricWeight x mu ≤
      anchorPairVariation metricWeight anchorWeight anchor x := by
  classical
  have hinner (i : ι) :
      anchorMass anchorWeight anchor * (x i - mu) ^ 2 ≤
        ∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2 := by
    have hexact :
        (∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2) =
          anchorMass anchorWeight anchor * (x i - mu) ^ 2 +
            ∑ j ∈ anchor, anchorWeight j * (x j - mu) ^ 2 := by
      have hcross :
          ∑ j ∈ anchor,
              (2 * (x i - mu)) * (anchorWeight j * (x j - mu)) = 0 := by
        rw [← Finset.mul_sum, hcenter, mul_zero]
      unfold anchorMass
      calc
        (∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2) =
            ∑ j ∈ anchor,
              (anchorWeight j * (x i - mu) ^ 2 +
                anchorWeight j * (x j - mu) ^ 2 -
                (2 * (x i - mu)) * (anchorWeight j * (x j - mu))) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (∑ j ∈ anchor, anchorWeight j) * (x i - mu) ^ 2 +
              ∑ j ∈ anchor, anchorWeight j * (x j - mu) ^ 2 -
              ∑ j ∈ anchor,
                (2 * (x i - mu)) * (anchorWeight j * (x j - mu)) := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                Finset.sum_mul]
        _ = (∑ j ∈ anchor, anchorWeight j) * (x i - mu) ^ 2 +
              ∑ j ∈ anchor, anchorWeight j * (x j - mu) ^ 2 := by
              rw [hcross]
              ring
    rw [hexact]
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg fun j hj =>
      mul_nonneg (hanchor j hj) (sq_nonneg _)
  unfold weightedDistance anchorPairVariation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hright :
      (∑ j ∈ anchor,
        metricWeight i * anchorWeight j * (x i - x j) ^ 2) =
        metricWeight i *
          (∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hright]
  have hmul := mul_le_mul_of_nonneg_left (hinner i) (hmetric i)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- A nonnegative graph whose anchor edges dominate a product measure
controls the weighted quotient distance.  This is the exact finite
multi-anchor estimate used after the Dickman kernel gap. -/
theorem half_kappa_anchorMass_mul_weightedDistance_le_dirichletEnergy
    (weight metricWeight : ι → ℝ) (kernel : ι → ι → ℝ)
    (anchor : Finset ι) (x : ι → ℝ) (mu kappa : ℝ)
    (hkappa : 0 ≤ kappa)
    (hweight : ∀ i, 0 ≤ weight i)
    (hmetric : ∀ i, 0 ≤ metricWeight i)
    (hkernel : ∀ i j, kernel i j ≤ 0)
    (hanchorEdge : ∀ i, ∀ j ∈ anchor,
      kappa * metricWeight i * weight j ≤
        weight i * weight j * (-kernel i j))
    (hcenter : ∑ j ∈ anchor, weight j * (x j - mu) = 0) :
    (kappa / 2) * anchorMass weight anchor *
        weightedDistance metricWeight x mu ≤
      dirichletEnergy weight kernel x := by
  classical
  have hpair :=
    anchorMass_mul_weightedDistance_le_anchorPairVariation
      metricWeight weight anchor x mu hmetric
      (fun j hj => hweight j) hcenter
  have hkpair :
      kappa * anchorPairVariation metricWeight weight anchor x ≤
        ∑ i, ∑ j,
          weight i * weight j * (-kernel i j) * (x i - x j) ^ 2 := by
    unfold anchorPairVariation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ anchor,
          kappa * (metricWeight i * weight j * (x i - x j) ^ 2)) ≤
          ∑ j ∈ anchor,
            weight i * weight j * (-kernel i j) * (x i - x j) ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hedge := hanchorEdge i j hj
            nlinarith [sq_nonneg (x i - x j)]
      _ ≤ ∑ j,
          weight i * weight j * (-kernel i j) * (x i - x j) ^ 2 := by
            apply Finset.sum_le_univ_sum_of_nonneg
            intro j
            exact mul_nonneg
              (mul_nonneg (mul_nonneg (hweight i) (hweight j))
                (neg_nonneg.mpr (hkernel i j))) (sq_nonneg _)
  have hscaled :
      kappa * anchorMass weight anchor *
          weightedDistance metricWeight x mu ≤
        kappa * anchorPairVariation metricWeight weight anchor x := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hpair hkappa
  unfold dirichletEnergy
  calc
    (kappa / 2) * anchorMass weight anchor *
        weightedDistance metricWeight x mu =
        (1 / 2 : ℝ) *
          (kappa * anchorMass weight anchor *
            weightedDistance metricWeight x mu) := by ring
    _ ≤ (1 / 2 : ℝ) *
        (kappa * anchorPairVariation metricWeight weight anchor x) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (∑ i, ∑ j,
          weight i * weight j * (-kernel i j) * (x i - x j) ^ 2) :=
      mul_le_mul_of_nonneg_left hkpair (by norm_num)

end Erdos390.Full.FiniteAnchoredDirichletQuadratic

end

/- Source module: Erdos390.Full.PrimeSquarefreeDirichletGeometry -/
section


/-!
# Prime-level Dirichlet geometry for the squarefree reference covariance

The squarefree Dickman reference matrix is conjugated here on the literal
finite prime band.  The conjugating coordinate is `x_p = c_p / t_p`, the
vertex weight is `t_p / p`, and the quotient metric is `t_p^2 / p`.
Consequently the graph distance to a constant is exactly

`sum_p (c_p - mu * t_p)^2 / p`.

All identities are finite and exact.  The only analytic input in the final
anchor theorem is the already proved uniform negativity of the Dickman
kernel quotient on a fixed interior block.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PrimeSquarefreeDirichletGeometry

open ArithmeticModel
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet
open FiniteAnchoredDirichletQuadratic
open SquarefreeCovarianceReference



variable {n W : ℕ}





















theorem tPrime_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < tPrime n p.1 := by
  have hp := prime_of_mem_primeBand p.2
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y hn0]
    exact mul_pos (by norm_num) (Scale.L_pos hn)
  unfold tPrime
  exact div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) hlogy

theorem primeWeight_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < primeWeight n p := by
  exact div_pos (tPrime_pos hn p) (by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos)

theorem primeMetricWeight_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < primeMetricWeight n p := by
  exact div_pos (sq_pos_of_pos (tPrime_pos hn p)) (by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos)

theorem primeKernel_symm (p q : PrimeIndex n W) :
    primeKernel n p q = primeKernel n q p := by
  exact covarianceKernel_comm _ _

theorem tPrime_mem_unit (hn : 1 < n) (p : PrimeIndex n W) :
    tPrime n p.1 ∈ Icc (0 : ℝ) 1 :=
  ⟨(tPrime_pos hn p).le,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn p.2⟩

/-- Exact conjugation of the separated prime reference quadratic. -/
theorem finiteReferenceQuadratic_eq_primeReferenceQuadratic
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) :
    referenceQuadratic (primeWeight n) (primeDiagonal n) (primeKernel n)
        (dirichletCoordinate n c) =
      primeReferenceQuadratic n c := by
  classical
  unfold referenceQuadratic primeReferenceQuadratic
  apply congrArg₂ (fun a b : ℝ ↦ a + b)
  · apply Finset.sum_congr rfl
    intro p hp
    unfold primeWeight primeDiagonal dirichletCoordinate
    have ht : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
    have hp0 : (p.1 : ℝ) ≠ 0 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
    field_simp [ht, hp0]
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    unfold primeWeight primeKernel dirichletCoordinate
    have htp : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
    have htq : tPrime n q.1 ≠ 0 := ne_of_gt (tPrime_pos hn q)
    have hp0 : (p.1 : ℝ) ≠ 0 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (prime_of_mem_primeBand q.2).ne_zero
    field_simp [htp, htq, hp0, hq0]

/-- Exact identification with the signed reference entries.  The extra
diagonal multiplier is counted once, while the kernel diagonal remains in
the full double sum. -/
theorem primeReferenceQuadratic_eq_entryQuadratic
    (c : PrimeIndex n W → ℝ) :
    primeReferenceQuadratic n c = primeReferenceEntryQuadratic n c := by
  classical
  have hentry (p q : PrimeIndex n W) :
      squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 +
          if p = q then DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) else 0 := by
    by_cases hpq : p = q
    · subst q
      simp [squarefreeReferenceEntry]
      ring
    · have hpqVal : p.1 ≠ q.1 := by
        intro h
        exact hpq (Subtype.ext h)
      simp [squarefreeReferenceEntry, hpq, hpqVal]
  have hdiag (p : PrimeIndex n W) :
      (∑ q, c p * c q *
        (if p = q then DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) else 0)) =
          DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) * c p ^ 2 := by
    rw [Finset.sum_eq_single p]
    · simp
      ring
    · intro q hq hqp
      simp [Ne.symm hqp]
    · simp
  have hkernel :
      (∑ p, ∑ q,
        covarianceKernel (tPrime n p.1) (tPrime n q.1) /
            ((p.1 : ℝ) * (q.1 : ℝ)) * c p * c q) =
        ∑ p, ∑ q, c p * c q * squarefreeKernelEntry n p.1 q.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    unfold squarefreeKernelEntry
    ring
  unfold primeReferenceQuadratic primeReferenceEntryQuadratic
  simp_rw [hentry, mul_add, Finset.sum_add_distrib, hdiag]
  rw [hkernel, add_comm]

/-- Exact prime reference decomposition, including the literal finite
row-sum residual. -/
theorem primeReferenceQuadratic_eq_dirichlet_add_residual
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) :
    primeReferenceQuadratic n c =
      dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) +
        ∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2 := by
  rw [← finiteReferenceQuadratic_eq_primeReferenceQuadratic hn c]
  exact referenceQuadratic_eq_dirichletEnergy_add_rowResidual
    (primeWeight n) (primeDiagonal n) (primeKernel n)
    (dirichletCoordinate n c) primeKernel_symm

/-- A row residual of relative size `epsilon * t_p` contributes at most
`epsilon` times the literal reciprocal coefficient square norm.  This is
the exact moving-low scaling: an additive `o(1)` row bound would not be
sufficient here. -/
theorem abs_rowResidualContribution_le
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) {epsilon : ℝ}
    (hresidual : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        epsilon * tPrime n p.1) :
    |∑ p, primeWeight n p *
        rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
          (dirichletCoordinate n c p) ^ 2| ≤
      epsilon * primeCoefficientL2Sq c := by
  classical
  have hterm (p : PrimeIndex n W) :
      |primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| ≤
        epsilon * ((1 / (p.1 : ℝ)) * c p ^ 2) := by
    have hw : 0 ≤ primeWeight n p := (primeWeight_pos hn p).le
    have hx : 0 ≤ (dirichletCoordinate n c p) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (hresidual p)
      (mul_nonneg hw hx)
    calc
      |primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| =
          (primeWeight n p * (dirichletCoordinate n c p) ^ 2) *
            |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hx]
              ring
      _ ≤ (primeWeight n p * (dirichletCoordinate n c p) ^ 2) *
          (epsilon * tPrime n p.1) := hmul
      _ = epsilon * ((1 / (p.1 : ℝ)) * c p ^ 2) := by
        unfold primeWeight dirichletCoordinate
        have ht : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
        have hp0 : (p.1 : ℝ) ≠ 0 := by
          exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
        field_simp [ht, hp0]
  calc
    |∑ p, primeWeight n p *
        rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
          (dirichletCoordinate n c p) ^ 2| ≤
        ∑ p, |primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, epsilon * ((1 / (p.1 : ℝ)) * c p ^ 2) :=
      Finset.sum_le_sum fun p hp ↦ hterm p
    _ = epsilon * primeCoefficientL2Sq c := by
      unfold primeCoefficientL2Sq
      rw [Finset.mul_sum]



/-- The conjugated metric is exactly the physical prime distance. -/
theorem weightedDistance_eq_primePhysicalDistance
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) (mu : ℝ) :
    weightedDistance (primeMetricWeight n) (dirichletCoordinate n c) mu =
      primePhysicalDistance n c mu := by
  classical
  unfold weightedDistance primePhysicalDistance
  apply Finset.sum_congr rfl
  intro p hp
  unfold primeMetricWeight dirichletCoordinate
  have ht : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
  have hp0 : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
  field_simp [ht, hp0]



theorem anchor_centered
    (anchor : Finset (PrimeIndex n W))
    (c : PrimeIndex n W → ℝ)
    (hmass : anchorMass (primeWeight n) anchor ≠ 0) :
    ∑ p ∈ anchor, primeWeight n p *
        (dirichletCoordinate n c p - anchorMean n anchor c) = 0 := by
  classical
  have hmass' : (∑ p ∈ anchor, primeWeight n p) ≠ 0 := by
    simpa only [anchorMass] using hmass
  unfold anchorMean anchorMass
  rw [show (∑ p ∈ anchor, primeWeight n p *
      (dirichletCoordinate n c p -
        (∑ q ∈ anchor, primeWeight n q * dirichletCoordinate n c q) /
          ∑ q ∈ anchor, primeWeight n q)) =
      ∑ p ∈ anchor,
        (primeWeight n p * dirichletCoordinate n c p -
          ((∑ q ∈ anchor,
              primeWeight n q * dirichletCoordinate n c q) /
            ∑ q ∈ anchor, primeWeight n q) * primeWeight n p) by
    apply Finset.sum_congr rfl
    intro p hp
    ring]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp [hmass']
  ring

/-- A prime in an interior anchor block supplies the exact edge domination
needed by the finite multi-anchor theorem. -/
theorem anchor_edge_domination
    (hn : 1 < n) {epsilon kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ q ∈ anchor,
      tPrime n q.1 ∈ Icc epsilon (1 - epsilon))
    (p : PrimeIndex n W) (q : PrimeIndex n W) (hq : q ∈ anchor) :
    kappa * primeMetricWeight n p * primeWeight n q ≤
      primeWeight n p * primeWeight n q * (-primeKernel n p q) := by
  have hqgap := hgap (tPrime n p.1) (tPrime_mem_unit hn p)
    (tPrime n q.1) (hinterior q hq)
  have hmul := mul_covarianceKernelQuotient_eq_kernel
    (s := tPrime n q.1) (t := tPrime n p.1)
    (tPrime_mem_unit hn q) (tPrime_mem_unit hn p)
  have hedge : kappa * tPrime n p.1 ≤
      -covarianceKernel (tPrime n p.1) (tPrime n q.1) := by
    rw [covarianceKernel_comm (tPrime n p.1) (tPrime n q.1)]
    nlinarith [tPrime_pos hn p]
  have hfactor : 0 ≤ primeWeight n p * primeWeight n q :=
    mul_nonneg (primeWeight_pos hn p).le (primeWeight_pos hn q).le
  calc
    kappa * primeMetricWeight n p * primeWeight n q =
        (primeWeight n p * primeWeight n q) *
          (kappa * tPrime n p.1) := by
      unfold primeMetricWeight primeWeight
      have hp0 : (p.1 : ℝ) ≠ 0 := by
        exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
      have hq0 : (q.1 : ℝ) ≠ 0 := by
        exact_mod_cast (prime_of_mem_primeBand q.2).ne_zero
      field_simp [hp0, hq0]
    _ ≤ (primeWeight n p * primeWeight n q) *
        (-covarianceKernel (tPrime n p.1) (tPrime n q.1)) :=
      mul_le_mul_of_nonneg_left hedge hfactor
    _ = primeWeight n p * primeWeight n q * (-primeKernel n p q) := by
      rfl



end Erdos390.Full.PrimeSquarefreeDirichletGeometry

end

/- Source module: Erdos390.Full.PaperBandQuadraticGeometry -/
section


/-!
# General band-vector Dirichlet gap

This is the quadratic-form part of the arithmetic bridge for an arbitrary
raw-gauge band vector.  It is deliberately separate from the compensated
slow coefficient used later in Lemma 8.6.  A band vector is lifted literally
to every prime in its cell; its reciprocal prime square norm is exactly the
`D`-norm, and its physical quotient distance dominates that norm by the
exact arithmetic centering identity.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBandQuadraticGeometry

open ArithmeticBandGeometry
open ArithmeticBandGeometry.Partition
open ArithmeticModel
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]



/-- Every literal reciprocal prime square norm is the corresponding
`WeightedBandData` prime norm. -/
theorem primeCoefficientL2Sq_eq_data_primeNormSq
    (P : Partition n W Band) (c : PrimeIndex n W → ℝ) :
    primeCoefficientL2Sq c = P.data.primeNormSq c := by
  unfold primeCoefficientL2Sq
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) * c p ^ 2 =
    (1 / (p.1 : ℝ)) * c p * c p
  ring

/-- The literal physical distance is the weighted prime norm after
subtracting the same arithmetic logarithmic coordinate. -/
theorem primePhysicalDistance_eq_data_primeNormSq
    (P : Partition n W Band) (c : PrimeIndex n W → ℝ) (mu : ℝ) :
    primePhysicalDistance n c mu =
      P.data.primeNormSq (fun p ↦ c p - mu * P.data.coord p) := by
  unfold primePhysicalDistance
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) * (c p - mu * tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) * (c p - mu * tPrime n p.1) *
      (c p - mu * tPrime n p.1)
  ring



/-- Subtracting the exact arithmetic least-squares physical direction
makes the prime coefficient orthogonal to `t`.  Hence every subsequent
constant representative in the conjugated Dirichlet coordinate can only
increase its reciprocal prime square norm. -/
theorem primeCoefficientL2Sq_le_physicalDistance_residualMinimizer
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (b : Band → ℝ) (nu : ℝ) :
    primeCoefficientL2Sq
        (P.data.residual b (P.data.physicalMinimizer b)) ≤
      primePhysicalDistance n
        (P.data.residual b (P.data.physicalMinimizer b)) nu := by
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  have hvariance : 0 ≤ P.variance :=
    P.data.primeNormSq_nonneg P.data.cellDeviation
  have hcoordPos : 0 < P.data.coordEnergy := by
    rw [P.data.coordEnergy_eq]
    exact add_pos_of_pos_of_nonneg (P.centerEnergy_pos hn) hvariance
  have hnormal : P.data.primeInner P.data.coord c = 0 := by
    simpa only [c] using
      P.data.physicalMinimizer_normal b hcoordPos.ne'
  have hnormal' : P.data.primeInner c P.data.coord = 0 := by
    rw [P.data.primeInner_comm]
    exact hnormal
  have hexpand :
      P.data.primeNormSq (fun p ↦ c p - nu * P.data.coord p) =
        P.data.primeNormSq c + nu ^ 2 * P.data.coordEnergy := by
    have hfun : (fun p ↦ c p - nu * P.data.coord p) =
        fun p ↦ c p + (-nu) * P.data.coord p := by
      funext p
      ring
    rw [hfun, P.data.primeNormSq_add, P.data.primeNormSq_smul,
      P.data.primeInner_smul_right, hnormal']
    unfold Erdos390.Lemma84.WeightedBandData.coordEnergy
    ring
  rw [primeCoefficientL2Sq_eq_data_primeNormSq P,
    primePhysicalDistance_eq_data_primeNormSq P, hexpand]
  exact le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (P.data.primeNormSq_nonneg P.data.coord))









end Erdos390.Full.PaperBandQuadraticGeometry

end

/- Source module: Erdos390.Full.PaperSquarefreeSlowQuadraticLower -/
section


/-!
# The literal squarefree slow lower bound

This file specializes the prime-level Dirichlet geometry to the paper's
actual compensated coefficient

`c_p = alpha_{j(p)} - t_p - q_{j(p)}`.

It proves three separate facts, so that their analytic inputs can be audited
independently:

1. the graph quotient distance is exactly the arithmetic `physicalSq`;
2. a relative finite row-residual estimate is absorbed by the literal
   compensated `L²` ledger;
3. signed entrywise squarefree-reference errors aggregate in the correct
   product-reciprocal and diagonal norms.

In particular, no squarefree variance lower bound occurs as a hypothesis.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperSquarefreeSlowQuadraticLower

open ArithmeticModel ArithmeticBandGeometry
open ArithmeticBandGeometry.Partition
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimePowerCovariance

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable (P : Partition n W Band)













/-- The second reciprocal diagonal costs one explicit cutoff factor. -/
theorem weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
    (hW : 0 < W) (c : Prime n W → ℝ) :
    weightedL2SqSecond (reciprocalWeight (n := n) (W := W)) c ≤
      (1 / (W : ℝ)) *
        weightedL2Sq (reciprocalWeight (n := n) (W := W)) c := by
  unfold weightedL2SqSecond weightedL2Sq reciprocalWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hWp : (W : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le
  have hinv : 1 / (p.1 : ℝ) ≤ 1 / (W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  have hrecip : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have hsq : 0 ≤ c p ^ 2 := sq_nonneg _
  calc
    (1 / (p.1 : ℝ)) ^ 2 * c p ^ 2 =
        (1 / (p.1 : ℝ)) * ((1 / (p.1 : ℝ)) * c p ^ 2) := by ring
    _ ≤ (1 / (W : ℝ)) * ((1 / (p.1 : ℝ)) * c p ^ 2) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hrecip hsq)
    _ = (1 / (W : ℝ)) * (1 / (p.1 : ℝ) * c p ^ 2) := by ring









/-- The separated reference quadratic is exactly the matrix quadratic of
the signed reference entries used in the squarefree profile theorem. -/
theorem matrixQuadratic_squarefreeReferenceEntry_eq_primeReference
    (c : Prime n W → ℝ) :
    matrixQuadratic
        (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1) c =
      primeReferenceQuadratic n c := by
  change primeReferenceEntryQuadratic n c = primeReferenceQuadratic n c
  exact (primeReferenceQuadratic_eq_entryQuadratic c).symm

/-- Signed entrywise profile estimates aggregate to a quantitative
squarefree-reference quadratic estimate. -/
theorem abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (c : Prime n W → ℝ)
    {epsilonOff epsilonDiag epsilonSecond : ℝ}
    (hentry : ∀ p r : Prime n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0) :
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
      epsilonOff * weightedL1 (reciprocalWeight (n := n) (W := W)) c ^ 2 +
        epsilonDiag * weightedL2Sq
          (reciprocalWeight (n := n) (W := W)) c +
        epsilonSecond * weightedL2SqSecond
          (reciprocalWeight (n := n) (W := W)) c := by
  unfold subtypeSquarefreeQuadratic
  rw [← matrixQuadratic_squarefreeReferenceEntry_eq_primeReference]
  exact abs_matrixQuadratic_sub_le
    (fun p r : Prime n W ↦ law.covII p.1 r.1)
    (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1)
    (reciprocalWeight (n := n) (W := W)) c hentry



end Erdos390.Full.PaperSquarefreeSlowQuadraticLower

end

/- Source module: Erdos390.Full.PaperActualSquarefreeSlowLower -/
section


/-!
# Actual squarefree slow lower from signed local profiles

The local one- and two-divisor profiles are first assembled through the
literal sigma mixture, so between-cell covariance is retained.  The resulting
signed entry estimate is then combined with the finite prime Dirichlet lower
from `PaperSquarefreeSlowQuadraticLower`.  Thus the genuine squarefree
variance lower is a conclusion, not an analytic hypothesis.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability OmittedTiltPairChamber
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open FixedFiniteMixturePrimePower
open PaperPrimePowerChamberError
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- Local signed profiles imply the literal actual-law entry comparison.
The proof passes through the exact sigma mixture, so it includes all
between-component covariance terms. -/
theorem actual_squarefree_reference_entry_bound_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 r.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 r.1| ≤
        (4 * pairCovarianceScale Eprofile) *
            reciprocalWeight p * reciprocalWeight r +
          if p = r then
            (2 * Eprofile) * reciprocalWeight p +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * reciprocalWeight p ^ 2
          else 0 := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight (B.actualComponentValuationLaw xi)
      B.n_gt_one hpair hsingle hKernel
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  intro p r
  have hpR : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
  have hrR : (r.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand r.2).ne_zero
  unfold reciprocalWeight
  convert hraw p r using 1
  split_ifs <;> field_simp [hpR, hrR]









end BridgeData

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalSlowKappa -/
section


/-!
# A fixed slow-direction Dickman gap

The compact interior anchor is always taken in `[1/8,7/8]`.  Hence its
Dickman quotient gap must be selected once, before `n`, the arithmetic mesh,
and every tilt parameter.  This file exposes that fixed choice and threads
it through the exact prime Dirichlet and squarefree lower bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalSlowKappa

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit PaperBridgeFit.BridgeData
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PrimePowerCovariance



theorem canonicalSlowKappa_pos : 0 < canonicalSlowKappa :=
  (Classical.choose_spec
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))).1

theorem canonicalSlowKappa_gap :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8),
      canonicalSlowKappa ≤ -covarianceKernelQuotient t s :=
  (Classical.choose_spec
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))).2

/-- Fixed-`kappa` version of the prime anchor Dirichlet lower. -/
theorem canonicalSlowKappa_primeDirichlet_anchor_lower
    {n W : ℕ} (hn : 1 < n)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ q ∈ anchor,
      tPrime n q.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor) :
    ∀ c : PrimeIndex n W → ℝ,
      (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor *
          primePhysicalDistance n c (anchorMean n anchor c) ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
  intro c
  rw [← weightedDistance_eq_primePhysicalDistance hn c]
  exact half_kappa_anchorMass_mul_weightedDistance_le_dirichletEnergy
    (primeWeight n) (primeMetricWeight n) (primeKernel n) anchor
    (dirichletCoordinate n c) (anchorMean n anchor c)
    canonicalSlowKappa canonicalSlowKappa_pos.le
    (fun p ↦ (primeWeight_pos hn p).le)
    (fun p ↦ (primeMetricWeight_pos hn p).le)
    (fun p q ↦ covarianceKernel_nonpos (tPrime_mem_unit hn p)
      (tPrime_mem_unit hn q))
    (anchor_edge_domination hn canonicalSlowKappa_gap anchor hinterior)
    (anchor_centered anchor c hmass.ne')



end Erdos390.Full.PaperCanonicalSlowKappa

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower PaperPrimePowerChamberError
open PaperWeightedInverseExport FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference PrimePowerCovariance
open PaperCanonicalSlowKappa

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

/- Source module: Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer -/
section


/-!
# Fixed-kappa actual band and nuisance-Schur gaps

This file is the fixed-constant counterpart of the existential quadratic
transfer in `PaperActualBandQuadraticTransfer`.  The structural constant is
the single continuum constant `PaperCanonicalSlowKappa.canonicalSlowKappa`;
it is therefore selected before the arithmetic mesh, the cutoff, and every
finite-`n` law.  All finite row, signed-profile, prime-power, and nuisance
losses remain displayed as coefficients of the literal arithmetic `D`-norm.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperBandQuadraticGeometry
open PaperCanonicalSlowKappa
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open FiniteSignedQuadraticEntryTransfer
open PaperSquarefreeSlowQuadraticLower
open SquarefreeCovarianceReference

variable {Omega : Type*} [Fintype Omega] {M n W : ℕ}
variable {Band : Type*} [Fintype Band] [DecidableEq Band]



theorem covarianceDifference_symm (law : BoundedValuationLaw Omega M)
    (p r : PrimeIndex n W) :
    law.covVV p.1 r.1 - law.covII p.1 r.1 =
      law.covVV r.1 p.1 - law.covII r.1 p.1 := by
  unfold covVV covII
  rw [law.probability.covariance_comm (law.V p.1) (law.V r.1),
    law.probability.covariance_comm (law.I p.1) (law.I r.1)]

/-- A literal normalized weighted row controls every symmetric coefficient
in the reciprocal-prime square norm. -/
theorem abs_subtypeFull_sub_squarefree_le_of_weightedRow
    (P : Partition n W Band)
    (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ) {R : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      (p.1 : ℝ) * ∑ r : PrimeIndex n W,
        |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤ R) :
    |subtypeFullQuadratic law c - subtypeSquarefreeQuadratic law c| ≤
      R * primeCoefficientL2Sq c := by
  let E : PrimeIndex n W → PrimeIndex n W → ℝ :=
    fun p r ↦ law.covVV p.1 r.1 - law.covII p.1 r.1
  have hsymm : ∀ p r, E p r = E r p := by
    intro p r
    exact covarianceDifference_symm law p r
  have hrow' : ∀ p : PrimeIndex n W,
      (∑ r : PrimeIndex n W, |E p r|) ≤ R * P.data.weight p := by
    intro p
    have hp : (0 : ℝ) < (p.1 : ℝ) := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    calc
      (∑ r : PrimeIndex n W, |E p r|) ≤ R / (p.1 : ℝ) :=
        (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hrow p)
      _ = R * P.data.weight p := by
        simp only [Partition.data, div_eq_mul_inv, one_mul]
  have hquad := P.data.symmetric_prime_row_quadratic_error
    E c R hsymm hrow'
  have hidentify :
      Erdos390.Lemma84.WeightedBandData.primeQuadratic E c =
        subtypeFullQuadratic law c - subtypeSquarefreeQuadratic law c := by
    unfold Erdos390.Lemma84.WeightedBandData.primeQuadratic
      subtypeFullQuadratic subtypeSquarefreeQuadratic matrixQuadratic E
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hidentify] at hquad
  simpa only [primeCoefficientL2Sq_eq_data_primeNormSq P] using hquad

/-- Weighted Cauchy--Schwarz for reciprocal prime coefficients. -/
theorem weightedL1_sq_le_totalWeight_mul_weightedL2Sq
    (c : PrimeIndex n W → ℝ) :
    weightedL1 (reciprocalWeight (n := n) (W := W)) c ^ 2 ≤
      (∑ p : PrimeIndex n W, reciprocalWeight p) *
        weightedL2Sq reciprocalWeight c := by
  let a : PrimeIndex n W → ℝ :=
    fun p ↦ Real.sqrt (reciprocalWeight p)
  let b : PrimeIndex n W → ℝ :=
    fun p ↦ Real.sqrt (reciprocalWeight p) * |c p|
  have hw (p : PrimeIndex n W) : 0 ≤ reciprocalWeight p := by
    unfold reciprocalWeight
    positivity
  have hsqa (p : PrimeIndex n W) : a p ^ 2 = reciprocalWeight p := by
    dsimp only [a]
    rw [Real.sq_sqrt (hw p)]
  have hsqb (p : PrimeIndex n W) : b p ^ 2 =
      reciprocalWeight p * c p ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hw p), sq_abs]
  have hab (p : PrimeIndex n W) : a p * b p =
      reciprocalWeight p * |c p| := by
    dsimp only [a, b]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hw p)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [hab, hsqa, hsqb] at hcs
  simpa only [weightedL1, weightedL2Sq] using hcs

/-- Signed squarefree-reference errors are relative to the reciprocal-prime
square norm, including the moving low prime range. -/
theorem abs_squarefree_sub_reference_le_relative
    (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ)
    {epsilonOff epsilonDiag epsilonSecond totalWeight invW : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hentry : ∀ p r : PrimeIndex n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0) :
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
      (epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW) *
        primeCoefficientL2Sq c := by
  have hbase := abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    law c hentry
  have hL1 := weightedL1_sq_le_totalWeight_mul_weightedL2Sq c
  have htotalNonneg : 0 ≤ ∑ p : PrimeIndex n W, reciprocalWeight p := by
    apply Finset.sum_nonneg
    intro p hp
    unfold reciprocalWeight
    positivity
  have htotalWeight : 0 ≤ totalWeight := htotalNonneg.trans hTotal
  have hL1' : weightedL1 reciprocalWeight c ^ 2 ≤
      totalWeight * weightedL2Sq reciprocalWeight c := by
    exact hL1.trans (mul_le_mul_of_nonneg_right hTotal (by
      unfold weightedL2Sq
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)))
  have hSecondBase := weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
    (n := n) (W := W) hW c
  have hSecond' : weightedL2SqSecond reciprocalWeight c ≤
      invW * weightedL2Sq reciprocalWeight c := by
    exact hSecondBase.trans (mul_le_mul_of_nonneg_right hInvW (by
      unfold weightedL2Sq
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)))
  have hL2id : weightedL2Sq reciprocalWeight c =
      primeCoefficientL2Sq c := rfl
  calc
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
        epsilonOff * weightedL1 reciprocalWeight c ^ 2 +
          epsilonDiag * weightedL2Sq reciprocalWeight c +
          epsilonSecond * weightedL2SqSecond reciprocalWeight c := hbase
    _ ≤ epsilonOff * (totalWeight * weightedL2Sq reciprocalWeight c) +
          epsilonDiag * weightedL2Sq reciprocalWeight c +
          epsilonSecond * (invW * weightedL2Sq reciprocalWeight c) := by
      gcongr
    _ = (epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW) *
          primeCoefficientL2Sq c := by
      rw [← hL2id]
      ring



/-- Strong fixed-kappa reference bound for the exact physical least-squares
residual of an arbitrary band vector.  The norm on the left is the literal
prime norm of that residual, before passing to the smaller band quotient
distance. -/
theorem canonicalSlowKappa_primeReference_physicalResidual_lower
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (b : Band → ℝ) :
    ((canonicalSlowKappa / 2) *
          anchorMass (primeWeight n) anchor - rowError) *
        primeCoefficientL2Sq
          (P.data.residual b (P.data.physicalMinimizer b)) ≤
      primeReferenceQuadratic n
        (P.data.residual b (P.data.physicalMinimizer b)) := by
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  let A : ℝ :=
    (canonicalSlowKappa / 2) * anchorMass (primeWeight n) anchor
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (div_nonneg canonicalSlowKappa_pos.le (by norm_num)) hmass.le
  have hdistance : primeCoefficientL2Sq c ≤
      primePhysicalDistance n c (anchorMean n anchor c) := by
    simpa only [c] using
      primeCoefficientL2Sq_le_physicalDistance_residualMinimizer
        P hn b (anchorMean n anchor c)
  have henergyLower :
      A * primeCoefficientL2Sq c ≤
        dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) := by
    exact (mul_le_mul_of_nonneg_left hdistance hA).trans (by
      simpa only [A] using
        canonicalSlowKappa_primeDirichlet_anchor_lower
          hn anchor hinterior hmass c)
  have hresidualAbs := abs_rowResidualContribution_le hn c hrow
  have hresidualLower :
      -(rowError * primeCoefficientL2Sq c) ≤
        ∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2 :=
    neg_le_of_abs_le hresidualAbs
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual hn c]
  dsimp only [c, A] at henergyLower hresidualLower ⊢
  linarith





/-- Fixed-kappa full-valuation bound for the exact physical residual of an
arbitrary band vector.  The comparison errors are measured in precisely the
same residual prime norm as the reference form. -/
theorem subtypeFull_physicalResidual_lower_canonicalKappa_of_entry_and_row
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n)
    (law : BoundedValuationLaw Omega M)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight n) anchor)
    {rowError epsilonOff epsilonDiag epsilonSecond totalWeight invW R : ℝ}
    (hOff : 0 ≤ epsilonOff) (hSecond : 0 ≤ epsilonSecond)
    (hW : 0 < W)
    (hTotal : (∑ p : PrimeIndex n W, reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1)
    (hentry : ∀ p r : PrimeIndex n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0)
    (hrowPower : ∀ p : PrimeIndex n W,
      (p.1 : ℝ) * ∑ r : PrimeIndex n W,
        |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤ R)
    (b : Band → ℝ) :
    ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight n) anchor -
            rowError -
            (epsilonOff * totalWeight + epsilonDiag +
              epsilonSecond * invW) - R) *
        primeCoefficientL2Sq
          (P.data.residual b (P.data.physicalMinimizer b)) ≤
      subtypeFullQuadratic law
        (P.data.residual b (P.data.physicalMinimizer b)) := by
  let c : PrimeIndex n W → ℝ :=
    P.data.residual b (P.data.physicalMinimizer b)
  let profileLoss : ℝ :=
    epsilonOff * totalWeight + epsilonDiag + epsilonSecond * invW
  have href := canonicalSlowKappa_primeReference_physicalResidual_lower
    P hn anchor hinterior hmass hrowReference b
  have hsf := abs_squarefree_sub_reference_le_relative law c
    hOff hSecond hW hTotal hInvW hentry
  have hfull := abs_subtypeFull_sub_squarefree_le_of_weightedRow
    P law c hrowPower
  have hsfLower :
      primeReferenceQuadratic n c -
          profileLoss * primeCoefficientL2Sq c ≤
        subtypeSquarefreeQuadratic law c := by
    have h := (abs_le.mp hsf).1
    simpa only [profileLoss] using (show
      primeReferenceQuadratic n c -
          profileLoss * primeCoefficientL2Sq c ≤
        subtypeSquarefreeQuadratic law c by linarith)
  have hfullLower :
      subtypeSquarefreeQuadratic law c - R * primeCoefficientL2Sq c ≤
        subtypeFullQuadratic law c := by
    have h := (abs_le.mp hfull).1
    linarith
  have hnorm : 0 ≤ primeCoefficientL2Sq c := by
    unfold primeCoefficientL2Sq
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (by positivity) (sq_nonneg _)
  dsimp only [c, profileLoss] at href hsfLower hfullLower hnorm ⊢
  nlinarith

/-- The exact arithmetic quotient distance is no larger than the prime norm
of the physical least-squares residual. -/
theorem bandNormSq_gaugePart_le_physicalResidual_primeCoefficientL2Sq
    [Nonempty Band]
    (P : Partition n W Band) (hn : 1 < n) (b : Band → ℝ) :
    P.data.bandNormSq (P.data.gaugePart b) ≤
      primeCoefficientL2Sq
        (P.data.residual b (P.data.physicalMinimizer b)) := by
  let q : Band → ℝ := P.data.gaugePart b
  let lambda : ℝ := P.data.gaugeCoefficient b
  have hq : P.data.inGauge q := by
    simpa only [q] using P.data.gaugePart_inGauge b
      (P.centerEnergy_pos hn).ne'
  have hdecomp : (fun j ↦ q j + lambda * P.center j) = b := by
    funext j
    exact P.data.gauge_decomposition b j
  have hvariance : 0 ≤ P.variance :=
    P.data.primeNormSq_nonneg P.data.cellDeviation
  have hphysical : P.data.bandNormSq q ≤
      P.data.physicalSq b (P.data.physicalMinimizer b) := by
    have h := P.data.physical_lower_bound q lambda hq hvariance
    rw [hdecomp] at h
    exact h
  rw [primeCoefficientL2Sq_eq_data_primeNormSq P]
  exact hphysical



end Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : PaperBridgeFit.BridgeData Head Band)





/-- The subtype full quadratic is exactly the variance of the corresponding
literal actual prime score. -/
theorem subtypeFullQuadratic_actual_eq_primeValuationScore_covariance
    [Nonempty Head]
    (xi : B.ParamSpace)
    (c : BandPrime B.sampleData.n B.sampleData.W → ℝ) :
    subtypeFullQuadratic (B.actualValuationLaw xi) c =
      (B.tiltedLaw xi).covariance
        (B.primeValuationScore c) (B.primeValuationScore c) := by
  unfold primeValuationScore
  rw [(B.tiltedLaw xi).covariance_sum_left]
  unfold subtypeFullQuadratic matrixQuadratic
    actualValuationLaw PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
  apply Finset.sum_congr rfl
  intro p hp
  rw [(B.tiltedLaw xi).covariance_sum_right]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(B.tiltedLaw xi).covariance_smul_left,
    (B.tiltedLaw xi).covariance_smul_right]
  ring









/-- Actual full-covariance lower bound for the exact physical residual of
an arbitrary band vector. -/
theorem actualFull_physicalResidual_lower_canonicalKappa_of_profiles_and_row
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (b : Band → ℝ) :
    let c := B.partition.data.residual b
      (B.partition.data.physicalMinimizer b)
    ((canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) - R) *
        primeCoefficientL2Sq c ≤
      (B.tiltedLaw xi).covariance
        (B.primeValuationScore c) (B.primeValuationScore c) := by
  dsimp only
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle hKernel
  have hfull :=
    subtypeFull_physicalResidual_lower_canonicalKappa_of_entry_and_row
      B.partition B.n_gt_one (B.actualValuationLaw xi)
      anchor hinterior hmass
      (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile))
      (add_nonneg (sq_nonneg _) hCKernel) hW hTotal hInvW
      hrowReference hentry hrowPower b
  rw [B.subtypeFullQuadratic_actual_eq_primeValuationScore_covariance xi
    (B.partition.data.residual b
      (B.partition.data.physicalMinimizer b))] at hfull
  exact hfull



/-- Arbitrary-band nuisance-Schur quotient gap for the exact physical
least-squares residual score.  This is the full quotient statement: `b` is
not assumed to lie in the arithmetic gauge, and the left side is the exact
finite distance represented by `bandNormSq (gaugePart b)`. -/
theorem actualPhysicalResidualSchur_fullQuotient_Dgap_canonicalKappa
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hsmall : rowError +
          ((4 * pairCovarianceScale Eprofile) * totalWeight +
            2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              CKernel) * invW) +
          R +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * totalWeight / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ b : Band → ℝ,
      let c := B.partition.data.residual b
        (B.partition.data.physicalMinimizer b)
      let F := B.primeValuationScore c
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R -
              ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                Cmarked ^ 2 * totalWeight / gamma)) *
            B.partition.data.bandNormSq (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
  intro b
  dsimp only
  let c := B.partition.data.residual b
    (B.partition.data.physicalMinimizer b)
  let F := B.primeValuationScore c
  let nuisanceLoss : ℝ :=
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      Cmarked ^ 2 * totalWeight / gamma
  have hfull := B.actualFull_physicalResidual_lower_canonicalKappa_of_profiles_and_row
    xi anchor hinterior hmass hEprofile hCKernel hW hTotal hInvW
    hrowReference hpair hsingle hKernel hrowPower b
  have hloss := B.nuisanceRegressionLoss_primeValuationScore_le_of_marked
    xi hgamma hCmarked hgapNuisance hTotal hmarked c
  have hvariance := B.nuisanceResidualScore_variance_identity
    xi hgamma hgapNuisance F
  have hstrong :
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R - nuisanceLoss) * primeCoefficientL2Sq c ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
    rw [hvariance]
    dsimp only [c, F, nuisanceLoss] at hfull hloss ⊢
    nlinarith
  have hdistance :=
    bandNormSq_gaugePart_le_physicalResidual_primeCoefficientL2Sq
      B.partition B.n_gt_one b
  have hcoef : 0 ≤
      (canonicalSlowKappa / 2) *
              anchorMass (primeWeight B.sampleData.n) anchor -
            rowError -
            ((4 * pairCovarianceScale Eprofile) * totalWeight +
              2 * Eprofile +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * invW) -
            R - nuisanceLoss := by
    dsimp only [nuisanceLoss]
    linarith
  dsimp only [c, F, nuisanceLoss] at hstrong ⊢
  exact (mul_le_mul_of_nonneg_left hdistance hcoef).trans hstrong



end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

/- Source module: Erdos390.Full.PaperCanonicalActualFullQuotientNullIdentification -/
section


/-!
# Exact prime-log null identification for the fixed-kappa quotient gap

The arithmetic quotient lower bound is naturally proved after minimizing the
coefficient `b_{j(p)} - mu t_p` over the physical logarithmic direction.  The
actual main score, however, carries a prescribed value of `mu` coming from
the stored slow coordinate.  This file proves at finite `n` that the two
scores have exactly the same nuisance-Schur quadratic form: their difference
is a multiple of `primeLogScore`, and the latter is an affine nuisance score.

No continuum limit or covariance approximation occurs here.  In particular,
the arbitrary band vector is retained throughout; the slow/`alpha` direction
is not discarded by restricting to the raw gauge.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









/-- Exact affine realization of a physical score plus an arbitrary tagged
head function inside the nuisance coordinates. -/
theorem physical_mul_add_headFunction_eq_inner_add_constant
    [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) (m : B.sampleData.Sample) :
    a * B.physicalScore m + B.headFunctionScore phi m =
      inner ℝ (B.physicalHeadNuisanceVector a phi)
          (B.nuisanceStatistic m) +
        B.physicalHeadAffineConstant phi := by
  rw [B.inner_nuisanceStatistic_eq_physical_add_headFunction]
  rw [B.headFunctionScore_decomposition phi m]
  unfold physicalHeadAffineConstant nuisanceHeadFunction headFunctionScore
  simp only [B.physicalHeadNuisanceVector_physical,
    B.physicalHeadNuisanceVector_head]
  change
    a * B.physicalScore m +
        (phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m) =
      a * B.physicalScore m +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) *
              (B.headIndicator h.1 m - B.headBaselineMass h.1) +
        (phi B.referenceHead +
          ∑ h : B.HeadIndex,
            (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1)
  have hsum :
      (∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) *
            (B.headIndicator h.1 m - B.headBaselineMass h.1)) +
        ∑ h : B.HeadIndex,
          (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1 =
      ∑ h : B.HeadIndex,
        (phi h.1 - phi B.referenceHead) * B.headIndicator h.1 m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [show
      a * B.physicalScore m +
            (∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) *
                (B.headIndicator h.1 m - B.headBaselineMass h.1)) +
          (phi B.referenceHead +
            ∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1) =
        a * B.physicalScore m + phi B.referenceHead +
          ((∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) *
                (B.headIndicator h.1 m - B.headBaselineMass h.1)) +
            ∑ h : B.HeadIndex,
              (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1) by
    ring, hsum]
  ring

/-- The covariance vector of a nuisance linear functional is the nuisance
covariance operator applied to its coefficient. -/
theorem nuisanceCovarianceVector_inner_nuisanceStatistic
    [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    B.nuisanceCovarianceVector xi
        (fun m => inner ℝ z (B.nuisanceStatistic m)) =
      B.nuisanceCovarianceOperator xi z := by
  apply ext_inner_left ℝ
  intro v
  rw [B.inner_nuisanceCovarianceVector,
    B.inner_nuisanceCovarianceOperator_bilinear]

/-- Regression recovers an exact nuisance linear functional. -/
theorem nuisanceCoefficientOfScore_inner_nuisanceStatistic
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m => inner ℝ z (B.nuisanceStatistic m)) = z := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.nuisanceCoefficientOfScore_solve,
    B.nuisanceCovarianceVector_inner_nuisanceStatistic]

/-- Hence the nuisance residual of a nuisance linear functional vanishes
pointwise, not merely in covariance. -/
theorem nuisanceResidualScore_inner_nuisanceStatistic
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceResidualScore xi hgamma hgap
        (fun m => inner ℝ z (B.nuisanceStatistic m)) =
      fun _ => 0 := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_inner_nuisanceStatistic]
  ring

/-- A deterministic score has zero nuisance covariance vector. -/
theorem nuisanceCovarianceVector_const
    [Nonempty Head]
    (xi : B.ParamSpace) (c : ℝ) :
    B.nuisanceCovarianceVector xi (fun _ => c) = 0 := by
  apply ext_inner_left ℝ
  intro z
  rw [B.inner_nuisanceCovarianceVector, inner_zero_right]
  unfold FiniteProbability.covariance
  rw [show (fun m => inner ℝ z (B.nuisanceStatistic m) * c) =
      fun m => c * inner ℝ z (B.nuisanceStatistic m) by
    funext m
    ring]
  rw [(B.tiltedLaw xi).expect_smul,
    (B.tiltedLaw xi).expect_const]
  ring

/-- The nuisance regression coefficient of a deterministic score is zero. -/
theorem nuisanceCoefficientOfScore_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (c : ℝ) :
    B.nuisanceCoefficientOfScore xi hgamma hgap (fun _ => c) = 0 := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.nuisanceCoefficientOfScore_solve,
    B.nuisanceCovarianceVector_const, map_zero]

/-- Constants survive nuisance regression unchanged. -/
theorem nuisanceResidualScore_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (c : ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun _ => c) = fun _ => c := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_const]
  simp

/-- The nuisance residual of an affine nuisance score is precisely its
deterministic affine part. -/
theorem nuisanceResidualScore_inner_add_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) (c : ℝ) :
    B.nuisanceResidualScore xi hgamma hgap
        (fun m => inner ℝ z (B.nuisanceStatistic m) + c) =
      fun _ => c := by
  rw [B.nuisanceResidualScore_add,
    B.nuisanceResidualScore_inner_nuisanceStatistic,
    B.nuisanceResidualScore_const]
  funext m
  simp

/-- Under the literal finite head-prime condition, `primeLogScore` has only
an affine nuisance residual. -/
theorem nuisanceResidualScore_primeLogScore_eq_const
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W) :
    B.nuisanceResidualScore xi hgamma hgap B.primeLogScore =
      fun _ => B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction := by
  have hscore : B.primeLogScore = fun m =>
      inner ℝ
          (B.physicalHeadNuisanceVector
            (1 / Real.log (ArithmeticModel.y B.sampleData.n))
            B.exactPrimeLogHeadFunction)
          (B.nuisanceStatistic m) +
        B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction := by
    funext m
    rw [B.primeLogScore_eq_explicit_physical_add_head hhead m]
    exact B.physical_mul_add_headFunction_eq_inner_add_constant
      (1 / Real.log (ArithmeticModel.y B.sampleData.n))
      B.exactPrimeLogHeadFunction m
  rw [hscore, B.nuisanceResidualScore_inner_add_const]

/-- Primewise form of the arithmetic physical residual score. -/
theorem primeValuationScore_residual_eq_band_sub_primeLog
    (b : Band → ℝ) (mu : ℝ) (m : B.sampleData.Sample) :
    B.primeValuationScore (B.partition.data.residual b mu) m =
      (∑ j : Band, b j * B.bandScore j m) - mu * B.primeLogScore m := by
  have hband :
      (∑ j : Band, b j * B.bandScore j m) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          b (B.partition.band p) *
            valuation p.1 (B.sampleData.value m) := by
    unfold bandScore
    rw [← Finset.sum_fiberwise Finset.univ B.partition.band
      (fun p : BandPrime B.sampleData.n B.sampleData.W =>
        b (B.partition.band p) *
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
  rw [hband]
  unfold primeValuationScore Erdos390.Lemma84.WeightedBandData.residual
    Erdos390.Lemma84.WeightedBandData.lift
    Erdos390.Lemma84.WeightedBandData.coord
    primeLogScore ArithmeticModel.tPrime ArithmeticBandGeometry.Partition.data
  simp only [ArithmeticModel.tPrime, div_eq_mul_inv]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Changing the physical subtraction parameter changes the prime score by
exactly a multiple of the prime-log nuisance direction. -/
theorem primeValuationScore_residual_change_mu
    (b : Band → ℝ) (mu nu : ℝ) :
    B.primeValuationScore (B.partition.data.residual b nu) =
      fun m =>
        B.primeValuationScore (B.partition.data.residual b mu) m +
          (mu - nu) * B.primeLogScore m := by
  funext m
  rw [B.primeValuationScore_residual_eq_band_sub_primeLog,
    B.primeValuationScore_residual_eq_band_sub_primeLog]
  ring







/-- Exact null relation needed by the full quotient gap: after nuisance
regression, changing `mu` adds only a deterministic constant. -/
theorem nuisanceResidualScore_residual_change_mu
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (b : Band → ℝ) (mu nu : ℝ) :
    B.nuisanceResidualScore xi hgamma hgap
        (B.primeValuationScore (B.partition.data.residual b nu)) =
      fun m =>
        B.nuisanceResidualScore xi hgamma hgap
            (B.primeValuationScore (B.partition.data.residual b mu)) m +
          (mu - nu) *
            B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction := by
  rw [B.primeValuationScore_residual_change_mu,
    B.nuisanceResidualScore_add, B.nuisanceResidualScore_smul,
    B.nuisanceResidualScore_primeLogScore_eq_const
      xi hgamma hgap hhead]





/-- Covariance is unchanged when a deterministic constant is added to both
copies of a score. -/
theorem covariance_add_const_self
    {Omega : Type*} [Fintype Omega]
    (law : Erdos390.Full.FiniteProbability Omega)
    (F : Omega → ℝ) (c : ℝ) :
    law.covariance (fun omega => F omega + c)
        (fun omega => F omega + c) = law.covariance F F := by
  have hconstLeft (G : Omega → ℝ) :
      law.covariance (fun _ => c) G = 0 := by
    unfold Erdos390.Full.FiniteProbability.covariance
    rw [law.expect_smul, law.expect_const]
    ring
  have hconstRight (G : Omega → ℝ) :
      law.covariance G (fun _ => c) = 0 := by
    rw [law.covariance_comm]
    exact hconstLeft G
  rw [law.covariance_add_left, law.covariance_add_right,
    law.covariance_add_right, hconstRight, hconstLeft, hconstLeft]
  ring

/-- The nuisance-Schur variance of the physical residual is independent of
the subtraction parameter `mu`.  This is the finite exact-null statement,
with no asymptotic hypothesis. -/
theorem nuisanceResidualVariance_residual_independent_mu
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (b : Band → ℝ) (mu nu : ℝ) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b nu)))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b nu))) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b mu)))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.primeValuationScore (B.partition.data.residual b mu))) := by
  rw [B.nuisanceResidualScore_residual_change_mu
    xi hgamma hgap hhead b mu nu]
  exact covariance_add_const_self
    (B.tiltedLaw xi)
    (B.nuisanceResidualScore xi hgamma hgap
      (B.primeValuationScore (B.partition.data.residual b mu)))
    ((mu - nu) *
      B.physicalHeadAffineConstant B.exactPrimeLogHeadFunction)

/-- Fixed-kappa full quotient gap for every arithmetic band vector and every
choice of the physical subtraction parameter.  The production lower bound is
proved at the exact arithmetic minimizer; `nuisanceResidualVariance_residual_independent_mu`
then transfers it by an equality, not an estimate, to the parameter carried
by the actual main/slow score. -/
theorem actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgapNuisance : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError Eprofile CKernel totalWeight invW R : ℝ}
    (hEprofile : 0 ≤ Eprofile) (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        reciprocalWeight p) ≤ totalWeight)
    (hInvW : (1 / (B.sampleData.W : ℝ)) ≤ invW)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hsmall : rowError +
          ((4 * pairCovarianceScale Eprofile) * totalWeight +
            2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              CKernel) * invW) +
          R +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * totalWeight / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor) :
    ∀ (b : Band → ℝ) (mu : ℝ),
      let c := B.partition.data.residual b mu
      let F := B.primeValuationScore c
      ((canonicalSlowKappa / 2) *
                anchorMass (primeWeight B.sampleData.n) anchor -
              rowError -
              ((4 * pairCovarianceScale Eprofile) * totalWeight +
                2 * Eprofile +
                ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                  CKernel) * invW) -
              R -
              ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                Cmarked ^ 2 * totalWeight / gamma)) *
            B.partition.data.bandNormSq (B.partition.data.gaugePart b) ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgapNuisance F)
          (B.nuisanceResidualScore xi hgamma hgapNuisance F) := by
  intro b mu
  dsimp only
  have hbase :=
    B.actualPhysicalResidualSchur_fullQuotient_Dgap_canonicalKappa
      xi hgamma hCmarked hgapNuisance anchor hinterior hmass
      hEprofile hCKernel hW hTotal hInvW hrowReference hpair hsingle
      hKernel hrowPower hmarked hsmall b
  have hnull := B.nuisanceResidualVariance_residual_independent_mu
    xi hgamma hgapNuisance hhead b
      (B.partition.data.physicalMinimizer b) mu
  rw [hnull]
  exact hbase



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeRowResidualEventually -/
section


/-!
# Relative prime-row residual for the squarefree Dickman reference

The prime-level anchored Dirichlet proof needs a *relative* row estimate.
An additive estimate for the Dickman kernel is not enough when the marked
prime coordinate tends to zero.  We therefore apply weighted Abel summation
to

`phi_s(t) = t * K(s,t)`.

Both `phi_s` and its derivative in `t` are `O(s)` uniformly on the unit
square.  Consequently the PNT remainder is `O(s / log(W)^3)`.  Kernel
symmetry and the removable quotient row-sum identity then turn this into the
literal bound

`|R_p| <= (D / log(W)^3 + two endpoint tails) * t_p`.

All constants below are chosen before `W`, the ambient integer, and the
marked prime.
-/

open scoped BigOperators
open Set Filter Topology

noncomputable section

namespace Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

open ArithmeticModel PrimeSums PrimeBandQuadrature
open KernelPrimeQuadrature ConditionedPoissonLimit DickmanBasic
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open MeasureTheory
open DoubleKernelPrimeQuadrature





lemma continuous_firstMomentKernel (s : ℝ) :
    Continuous (firstMomentKernel s) := by
  exact continuous_id.mul (continuous_covarianceKernel_left s)

lemma continuous_firstMomentKernelDerivative (s : ℝ) :
    Continuous (firstMomentKernelDerivative s) := by
  exact (continuous_covarianceKernel_left s).add
    (continuous_id.mul
      (continuous_covarianceKernelDerivativeSecondExtension_left s))

lemma hasDerivAt_firstMomentKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (firstMomentKernel s)
      (firstMomentKernelDerivative s t) t := by
  have hK := hasDerivAt_covarianceKernel_second hs ht
  have hExt := covarianceKernelDerivativeSecondExtension_eq hs ht
  simpa only [firstMomentKernel, firstMomentKernelDerivative, id_eq,
    one_mul, hExt] using (hasDerivAt_id t).mul hK





lemma hasDerivAt_firstMomentAbelCoefficient
    {s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (firstMomentAbelCoefficient s z)
      (firstMomentAbelDerivative s z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  exact hasDerivAt_weightedAbelCoefficient
    (firstMomentKernel s) (firstMomentKernelDerivative s) hz hx
      (hasDerivAt_firstMomentKernel_second hs ht)

lemma deriv_firstMomentAbelCoefficient
    {s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    deriv (firstMomentAbelCoefficient s z) x =
      firstMomentAbelDerivative s z x := by
  exact (hasDerivAt_firstMomentAbelCoefficient hs hz hx hxz).deriv

lemma continuousOn_firstMomentAbelDerivative
    (s z : ℝ) (hz : 1 < z) {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn (firstMomentAbelDerivative s z) (Icc A Y) := by
  intro x hx
  exact continuousAt_weightedAbelCoefficientDerivative
    (firstMomentKernel s) (firstMomentKernelDerivative s)
    (continuous_firstMomentKernel s)
    (continuous_firstMomentKernelDerivative s) hz
      (hA.trans_le hx.1) |>.continuousWithinAt

lemma integrableOn_deriv_firstMomentAbelCoefficient
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (firstMomentAbelCoefficient s z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (firstMomentAbelDerivative s z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_firstMomentAbelDerivative s z hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    exact deriv_firstMomentAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_firstMoment_mul_theta
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := firstMomentAbelDerivative s z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_firstMomentAbelDerivative s z hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change firstMomentAbelDerivative s z x * Chebyshev.theta x =
    deriv (firstMomentAbelCoefficient s z) x * Chebyshev.theta x
  congr 1
  exact (deriv_firstMomentAbelCoefficient hs hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_firstMoment_mul_id
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => firstMomentAbelDerivative s z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_firstMomentAbelDerivative s z hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change firstMomentAbelDerivative s z x * x =
    deriv (firstMomentAbelCoefficient s z) x * x
  congr 1
  exact (deriv_firstMomentAbelCoefficient hs hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

/-- Exact prime-cell identity before estimating the PNT remainder. -/
theorem firstMomentKernel_primeCell_sub_continuum_eq_remainder
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    fullWeightedReciprocalSum (firstMomentKernel s) z Y -
        fullWeightedReciprocalSum (firstMomentKernel s) z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), firstMomentKernel s t / t) =
      weightedAbelRemainder (firstMomentKernel s) z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ
        (weightedAbelCoefficient (firstMomentKernel s) z) x := by
    intro x hx
    change DifferentiableAt ℝ (firstMomentAbelCoefficient s z) x
    exact (hasDerivAt_firstMomentAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint : IntegrableOn
      (deriv (weightedAbelCoefficient (firstMomentKernel s) z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
    simpa only [firstMomentAbelCoefficient] using
      integrableOn_deriv_firstMomentAbelCoefficient hs hz hYz
  have hThetaInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
    simpa only [firstMomentAbelCoefficient] using
      intervalIntegrable_deriv_firstMoment_mul_theta hs hz hY hYz
  have hMainInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
    simpa only [firstMomentAbelCoefficient] using
      intervalIntegrable_deriv_firstMoment_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ =>
          deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
      apply hThetaInt.mono_set
      rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
      intro x hx
      exact ⟨hAR.trans hx.1, hx.2⟩
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hdecomp :=
    fullWeightedReciprocalSum_interval_sub_main_eq_remainder
      (firstMomentKernel s) z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral
    (firstMomentKernel s) (continuous_firstMomentKernel s)
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp











/-- Box-independent, relative one-index quadrature for the exact test
function occurring in the prime row. -/
theorem exists_uniform_firstMomentKernel_primeCell_relative_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 1 < z →
      ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |fullWeightedReciprocalSum (firstMomentKernel s) z Y -
            fullWeightedReciprocalSum (firstMomentKernel s) z A -
            (∫ t in realLogCoordinate z (A : ℝ)..
              realLogCoordinate z (Y : ℝ), firstMomentKernel s t / t)| ≤
          (D / Real.log (A : ℝ) ^ 3) * s := by
  obtain ⟨Ctheta, hCtheta, Xtheta, hTheta⟩ :=
    exists_thetaError_log_cube_bound
  obtain ⟨Ckernel, hCkernel, hKernelProduct⟩ := kernel_product_bound
  obtain ⟨Cderiv, hCderiv, hDerivative⟩ :=
    kernel_secondDerivative_first_bound
  let M : ℝ := Ckernel + Cderiv
  have hM : 0 < M := add_pos hCkernel hCderiv
  have hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u := by
    intro u hu t ht
    have hK : |covarianceKernel u t| ≤ Ckernel * u * t := by
      simpa only [covarianceKernel] using hKernelProduct u hu t ht
    rw [firstMomentKernel, abs_mul, abs_of_nonneg ht.1]
    calc
      t * |covarianceKernel u t| ≤ t * (Ckernel * u * t) :=
        mul_le_mul_of_nonneg_left hK ht.1
      _ = (Ckernel * u) * t ^ 2 := by ring
      _ ≤ (Ckernel * u) * 1 := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hCkernel.le hu.1)
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
      _ ≤ M * u := by
        dsimp only [M]
        nlinarith [mul_nonneg hCderiv.le hu.1]
  have hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u := by
    intro u hu t ht
    have hK : |covarianceKernel u t| ≤ Ckernel * u * t := by
      simpa only [covarianceKernel] using hKernelProduct u hu t ht
    have hExt := covarianceKernelDerivativeSecondExtension_eq hu ht
    have hD : |covarianceKernelDerivativeSecondExtension u t| ≤
        Cderiv * u := by
      rw [hExt]
      exact hDerivative u hu t ht
    unfold firstMomentKernelDerivative
    calc
      |covarianceKernel u t +
          t * covarianceKernelDerivativeSecondExtension u t| ≤
        |covarianceKernel u t| +
          |t * covarianceKernelDerivativeSecondExtension u t| :=
        abs_add_le _ _
      _ = |covarianceKernel u t| +
          t * |covarianceKernelDerivativeSecondExtension u t| := by
        rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ Ckernel * u * t + t * (Cderiv * u) := by
        exact add_le_add hK (mul_le_mul_of_nonneg_left hD ht.1)
      _ ≤ M * u := by
        dsimp only [M]
        have hk : Ckernel * u * t ≤ Ckernel * u := by
          exact mul_le_of_le_one_right
            (mul_nonneg hCkernel.le hu.1) ht.2
        have hd : t * (Cderiv * u) ≤ Cderiv * u := by
          rw [mul_comm]
          exact mul_le_of_le_one_right
            (mul_nonneg hCderiv.le hu.1) ht.2
        linarith
  obtain ⟨N, hN⟩ := exists_nat_gt Xtheta
  let D : ℝ := 6 * (Ctheta * M)
  refine ⟨D, by dsimp only [D]; positivity, max N 2, ?_⟩
  intro s hs z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hThetaCell : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ Ctheta * x / Real.log x ^ 3 := by
    intro x hx
    apply hTheta x
    exact le_trans (le_of_lt hN) (by exact_mod_cast hNA) |>.trans hx.1
  rw [firstMomentKernel_primeCell_sub_continuum_eq_remainder
    hs hz hA2 hAY hYz]
  have hbound := abs_firstMomentWeightedAbelRemainder_le
    hCtheta.le hM.le hs hz hA2 hAY hYz hPhi hPhiPrime hThetaCell
  calc
    _ ≤ 6 * (Ctheta * M) * s / Real.log (A : ℝ) ^ 3 := hbound
    _ = (D / Real.log (A : ℝ) ^ 3) * s := by
      dsimp only [D]
      ring















/-- Uniform literal prime-row theorem.  The constant multiplying
`log(W)^{-3}` is selected before the cutoff and before the ambient integer. -/
theorem exists_uniform_primeRowResidual_relative_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ {n W : ℕ}, 1 < n → X₀ ≤ W → W ≤ yNat n →
        ∀ p : PrimeIndex n W,
          |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
            primeRowRelativeError D C n W * tPrime n p.1 := by
  obtain ⟨D, hD, Xquad, hquad⟩ :=
    exists_uniform_firstMomentKernel_primeCell_relative_bound
  obtain ⟨C, hC, hKernel⟩ := kernel_product_bound
  refine ⟨D, hD, C, hC, max Xquad 2, ?_⟩
  intro n W hn hW hWY p
  have hW2 : 2 ≤ W := (le_max_right Xquad 2).trans hW
  have hXquad : Xquad ≤ W := (le_max_left Xquad 2).trans hW
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hrelative : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator (y n) W (yNat n) (firstMomentKernel s) -
          (∫ t in realLogCoordinate (y n) (W : ℝ)..
            realLogCoordinate (y n) (yNat n : ℝ),
              firstMomentKernel s t / t)| ≤
        (D / Real.log (W : ℝ) ^ 3) * s := by
    intro s hs
    simpa only [primeCellOperator] using
      hquad s hs (y n) hy W (yNat n) hXquad hWY hyNatY
  exact abs_primeRowResidual_le_of_relative_quadrature hC.le hn hW2 hWY
    (by
      intro u hu t ht
      simpa only [covarianceKernel] using hKernel u hu t ht)
    hrelative p

theorem tendsto_primeRowRelativeError_fixedCutoff
    (D C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ primeRowRelativeError D C n W)
      atTop (nhds (D / Real.log (W : ℝ) ^ 3)) := by
  have hbase : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (W : ℝ)) atTop (nhds 0) := by
    simpa only using
      _root_.Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_fixed_cutoffCoordinate_zero W
  have htopRaw :=
    _root_.Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_floor_scalePoint_coordinate
      (t := (1 : ℝ)) (by norm_num)
  have htop : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (yNat n : ℝ)) atTop (nhds 1) := by
    apply htopRaw.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    unfold yNat RegularMeshPrimeCutoffs.scalePoint
    rw [one_mul, Real.exp_log (Scale.y_pos hn)]
  have htail : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (W : ℝ) +
        (1 - realLogCoordinate (y n) (yNat n : ℝ)))
      atTop (nhds 0) := by
    simpa only [sub_self, add_zero] using
      hbase.add ((tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub htop)
  have hscaled := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ C) atTop (nhds C)).mul htail
  have hconst : Tendsto (fun _n : ℕ ↦
      D / Real.log (W : ℝ) ^ 3) atTop
      (nhds (D / Real.log (W : ℝ) ^ 3)) := tendsto_const_nhds
  simpa only [primeRowRelativeError, mul_zero, add_zero] using
    hconst.add hscaled

/-- Fully eventual relative row terminal.  Given any prescribed positive
row tolerance, one cutoff threshold works for every larger cutoff; after
that choice the literal row bound holds for every sufficiently large
ambient integer and every marked prime. -/
theorem exists_cutoff_eventually_primeRowResidual_le
    {target : ℝ} (htarget : 0 < target) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ p : PrimeIndex n W,
        |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
          target * tPrime n p.1 := by
  obtain ⟨D, hD, C, hC, Xrow, hrow⟩ :=
    exists_uniform_primeRowResidual_relative_bound
  have hLogTop : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun W : ℕ ↦ (Real.log (W : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLogTop
  have hFixed : Tendsto (fun W : ℕ ↦
      D / Real.log (W : ℝ) ^ 3) atTop (nhds 0) := by
    have hmain := (tendsto_const_nhds : Tendsto
      (fun _W : ℕ ↦ D) atTop (nhds D)).mul (hInv.pow 3)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero,
      zero_pow (by norm_num : 3 ≠ 0)] using hmain
  have hFixedSmall : ∀ᶠ W : ℕ in atTop,
      D / Real.log (W : ℝ) ^ 3 < target / 2 :=
    hFixed.eventually (eventually_lt_nhds (half_pos htarget))
  obtain ⟨Wsmall, hWsmall⟩ := eventually_atTop.1 hFixedSmall
  refine ⟨max Xrow Wsmall, ?_⟩
  intro W hW
  have hXrow : Xrow ≤ W := (le_max_left Xrow Wsmall).trans hW
  have hWsmall' : Wsmall ≤ W := (le_max_right Xrow Wsmall).trans hW
  have hfixedW : D / Real.log (W : ℝ) ^ 3 < target / 2 :=
    hWsmall W hWsmall'
  have herrorT := tendsto_primeRowRelativeError_fixedCutoff D C W
  have herrorSmall : ∀ᶠ n : ℕ in atTop,
      primeRowRelativeError D C n W < target :=
    herrorT.eventually (eventually_lt_nhds (by linarith))
  have hyNatTop : Tendsto (fun n : ℕ ↦ yNat n) atTop atTop := by
    unfold yNat
    exact tendsto_nat_floor_atTop.comp
      Erdos390.Full.RegularMeshPrimeCutoffs.tendsto_y_atTop
  have hWY : ∀ᶠ n : ℕ in atTop, W ≤ yNat n :=
    hyNatTop.eventually (eventually_ge_atTop W)
  filter_upwards [eventually_gt_atTop 1, hWY, herrorSmall] with
      n hn hWYn herrorN
  intro p
  have hraw := hrow hn hXrow hWYn p
  exact hraw.trans (mul_le_mul_of_nonneg_right herrorN.le
    (tPrime_mem_unit hn p).1)

end Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

end

/- Source module: Erdos390.Full.PaperLemma84StructuralCutoff -/
section


/-!
# Structural cutoff for the arithmetic quotient gap

The constants and cutoff in this file precede the mesh, the finite head
type, the exact head patterns, and every later tilt box.  Only vanishing
remainders will be selected after those data in the eventual theorem.
-/

open Filter Topology

namespace Erdos390.Full.PaperLemma84StructuralCutoff

noncomputable section

open ArithmeticModel
open PaperCanonicalSlowKappa
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit.BridgeData
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic







theorem quotientMain_pos : 0 < quotientMain := by
  exact div_pos canonicalSlowKappa_pos (by norm_num)

theorem quotientRowTarget_pos : 0 < quotientRowTarget := by
  exact div_pos quotientMain_pos (by norm_num)

theorem quotientKappa_pos : 0 < quotientKappa := by
  exact div_pos quotientMain_pos (by norm_num)

/-- All non-vanishing arithmetic losses can be made small by one cutoff
chosen before the mesh and the head-pattern family. -/
theorem exists_structural_cutoff :
    ∃ CKernel : ℝ, 0 ≤ CKernel ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |ConditionedPoissonLimit.covarianceKernel s t| ≤ CKernel * t) ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        2 ≤ W ∧
        RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W ∧
        (∀ᶠ n : ℕ in atTop, ∀ p : PrimeIndex n W,
          |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
            quotientRowTarget * tPrime n p.1) ∧
        quotientRowTarget +
            signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
            FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant *
              (1 / (W : ℝ)) <
          quotientMain / 4 := by
  obtain ⟨CKernel, hCKernel, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  obtain ⟨Wrow, hrow⟩ :=
    PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      quotientRowTarget_pos
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let tailConstant : ℝ := signedSecondConstant 0 CKernel + Cpow
  have hInv : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ)) atTop (nhds 0) := by
    have hcast : Tendsto (fun W : ℕ ↦ (W : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hcast
  have htail : Tendsto
      (fun W : ℕ ↦ tailConstant * (1 / (W : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hInv
  have hsmall : ∀ᶠ W : ℕ in atTop,
      tailConstant * (1 / (W : ℝ)) < quotientMain / 16 :=
    htail.eventually (eventually_lt_nhds
      (div_pos quotientMain_pos (by norm_num)))
  obtain ⟨Wtail, hWtail⟩ := eventually_atTop.1 hsmall
  let W₀ := max 2
    (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff
      (max Wrow Wtail))
  refine ⟨CKernel, hCKernel, hKernel, W₀, ?_⟩
  intro W hW
  have htwo : 2 ≤ W := (le_max_left 2 _).trans hW
  have hanchor :
      RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W :=
    ((le_max_left _ (max Wrow Wtail)).trans (le_max_right 2 _)).trans hW
  have hrowW : Wrow ≤ W :=
    ((le_max_left Wrow Wtail).trans
      (le_max_right _ (max Wrow Wtail))).trans (le_max_right 2 _ |>.trans hW)
  have htailW : Wtail ≤ W :=
    ((le_max_right Wrow Wtail).trans
      (le_max_right _ (max Wrow Wtail))).trans (le_max_right 2 _ |>.trans hW)
  have htailSmall := hWtail W htailW
  refine ⟨htwo, hanchor, hrow W hrowW, ?_⟩
  have hid :
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
          Cpow * (1 / (W : ℝ)) =
        tailConstant * (1 / (W : ℝ)) := by
    dsimp only [tailConstant]
    ring
  change quotientRowTarget +
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
        Cpow * (1 / (W : ℝ)) < quotientMain / 4
  rw [show quotientRowTarget +
        signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
          Cpow * (1 / (W : ℝ)) =
      quotientRowTarget + tailConstant * (1 / (W : ℝ)) by
        rw [← hid]
        ring]
  dsimp only [quotientRowTarget]
  linarith [quotientMain_pos]

end
end Erdos390.Full.PaperLemma84StructuralCutoff

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

/- Source module: Erdos390.Full.PaperCanonicalFullQuotientEventually -/
section


/-!
# The canonical actual-full arithmetic quotient gap

This file discharges every analytic input of the finite full-valuation
quotient theorem.  The structural cutoff is selected before the mesh, the
head patterns, and the effective tilt ball.  Once those later data are fixed,
only the ambient threshold is allowed to depend on them.

The conclusion is the actual nuisance-Schur covariance of the literal
full-valuation score.  No projected inverse, profile estimate, prime-power
row, nuisance gap, or convergence statement is accepted as a hypothesis.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PrimeSums
open RegularMeshPrimeCutoffs
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open PaperCanonicalSlowKappa
open PaperLemma84StructuralCutoff
open SquarefreeSharpBandTransfer PrimePowerSharpBandTransfer
open PaperPrimePowerChamberError

namespace BridgeData

/-- A product-log rate and pointwise nonnegativity imply ordinary
convergence to zero. -/
private theorem tendsto_zero_of_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 ≤ epsilon n)
    (hrate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hlogOne] with n hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (hepsilon n)
  exact squeeze_zero' (Filter.Eventually.of_forall hepsilon) hupper hrate

set_option maxHeartbeats 4000000 in
/-- Exact paper-order eventual form of the full arithmetic quotient gap.

The exact head condition is deliberately placed after `W`; it both supplies
the finite logarithmic null relation and implies the support condition used
by all marked asymptotics. -/
theorem exists_structural_cutoff_eventually_canonical_actualFullQuotient :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      ∀ (anchors : Finset (Fin M.cellCount))
        (_hAnchors : anchors.Nonempty)
        (_hIdealLower : ∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k)
        (_hIdealUpper : ∀ k ∈ anchors,
          M.upper k ≤ 1 - (1 / 8 : ℝ))
        (_hIdealMass : (1 : ℝ) / 8 ≤
          (∑ k ∈ anchors, M.width k) / 2),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern)
        (_hhead : ∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W),
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ) (_hmarginFloor : 0 < marginFloor),
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
          (_hBn : B.sampleData.n = n) (_hBW : B.sampleData.W = W)
          (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
              hsep hremaining) →
          (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
            B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          ∀ (T : BarycentricTarget B.sampleData)
            (_hTmargin : marginFloor ≤ T.cellMassMargin)
            (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
          let xi : B.ParamSpace := B.effectiveParamEquiv z
          let gamma : ℝ :=
            B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
          let hgamma : 0 < gamma :=
            B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
          let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
            intro v
            simpa only [gamma, xi] using
              B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz v
          ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
            kappa * B.partition.data.bandNormSq
                (B.partition.data.gaugePart b) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨CKernel, hCKernel, hKernelStructural,
      Wstruct, hstruct⟩ := PaperLemma84StructuralCutoff.exists_structural_cutoff
  refine ⟨quotientKappa, quotientKappa_pos, Wstruct, ?_⟩
  intro W hWstruct delta eta M hdelta anchors hAnchors
    hIdealLower hIdealUpper hIdealMass Head _instFintype
    _instDecidable _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmarginFloor
  obtain ⟨hW2, hWanchor, hrowEvent, hstructSmall⟩ := hstruct W hWstruct
  have hWone : 1 < W := by omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpow, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger W hWone
        hHeadLe a
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
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
  have hcombinedT : Tendsto combined atTop (nhds 0) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogOne : ∀ᶠ n : ℕ in atTop,
        1 ≤ Real.log (Scale.L n) :=
      (Real.tendsto_log_atTop.comp hLTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    have hupper : ∀ᶠ n : ℕ in atTop,
        combined n ≤ combined n * Real.log (Scale.L n) := by
      filter_upwards [hcombinedNonneg, hlogOne] with n hn hlog
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hn
    exact squeeze_zero' hcombinedNonneg hupper hcombinedRate
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero markedError hmarked0 hmarkedRate
  let H : ℕ → ℝ := fun n ↦ 12 * Real.log (Scale.L n)
  let K : ℝ := 2 * Real.log 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hprofileH : Tendsto (fun n : ℕ ↦ profileError n * H n)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ (12 : ℝ))
        atTop (nhds 12) := tendsto_const_nhds
    have h := hconst.mul hprofileRate
    simpa only [H, mul_zero, zero_mul, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hpairH : Tendsto
      (fun n : ℕ ↦ pairCovarianceScale (profileError n) * H n)
        atTop (nhds 0) := by
    have hlinear : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
          (profileError n * H n)) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hprofileH
    have hsquare : Tendsto (fun n : ℕ ↦
        profileError n * (profileError n * H n)) atTop (nhds 0) := by
      simpa only [mul_zero] using hprofileT.mul hprofileH
    have hsum := hlinear.add hsquare
    have hsum0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
            (profileError n * H n) +
          profileError n * (profileError n * H n))
        atTop (nhds 0) := by simpa only [zero_add] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold pairCovarianceScale
    ring
  have hsignedT : Tendsto
      (fun n : ℕ ↦ signedSecondConstant (profileError n) CKernel)
        atTop (nhds (signedSecondConstant 0 CKernel)) := by
    have hcont : Continuous
        (fun x : ℝ ↦ signedSecondConstant x CKernel) := by
      unfold signedSecondConstant
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprofileT
  have hmarkedH : Tendsto (fun n : ℕ ↦ markedError n ^ 2 * H n)
      atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ ↦
        markedError n * (markedError n * Real.log (Scale.L n)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hmarkedT.mul hmarkedRate
    have hconst : Tendsto (fun _n : ℕ ↦ (12 : ℝ))
        atTop (nhds 12) := tendsto_const_nhds
    have h := hconst.mul hbase
    simpa only [H, mul_zero, zero_mul, pow_two, mul_assoc, mul_left_comm,
      mul_comm]
      using h
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let dcard : ℝ := (Fintype.card Head + 1 : ℕ)
  have hdcard : 0 ≤ dcard := by dsimp only [dcard]; positivity
  let R : ℕ → ℝ := fun n ↦
    Cpow * (1 / (W : ℝ)) + epsilon75 n + combined n
  have hRT : Tendsto R atTop
      (nhds (Cpow * (1 / (W : ℝ)))) := by
    simpa only [R, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  let nuisanceMajorant : ℕ → ℝ := fun n ↦
    dcard * markedError n ^ 2 * H n / gammaFloor
  have hnuisanceT : Tendsto nuisanceMajorant atTop (nhds 0) := by
    have hnum : Tendsto (fun n : ℕ ↦
        dcard * (markedError n ^ 2 * H n)) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hmarkedH
    have hdiv := hnum.div
      (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ gammaFloor)
        atTop (nhds gammaFloor)) hgammaFloor.ne'
    simpa only [nuisanceMajorant, zero_div, mul_assoc] using hdiv
  let loss : ℕ → ℝ := fun n ↦
    quotientRowTarget +
      ((4 * pairCovarianceScale (profileError n)) * H n +
        2 * profileError n +
        signedSecondConstant (profileError n) CKernel *
          (1 / (W : ℝ))) +
      R n + nuisanceMajorant n
  let limitLoss : ℝ :=
    quotientRowTarget +
      signedSecondConstant 0 CKernel * (1 / (W : ℝ)) +
      Cpow * (1 / (W : ℝ))
  have hlossT : Tendsto loss atTop (nhds limitLoss) := by
    have hoff : Tendsto (fun n : ℕ ↦
        (4 * pairCovarianceScale (profileError n)) * H n)
        atTop (nhds 0) := by
      have h := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (4 : ℝ))
        atTop (nhds 4)).mul hpairH
      simpa only [mul_zero, mul_assoc] using h
    have hdiag : Tendsto (fun n : ℕ ↦ 2 * profileError n)
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hprofileT
    have hsecond : Tendsto (fun n : ℕ ↦
        signedSecondConstant (profileError n) CKernel *
          (1 / (W : ℝ)))
        atTop (nhds (signedSecondConstant 0 CKernel *
          (1 / (W : ℝ)))) := hsignedT.mul tendsto_const_nhds
    have hrow : Tendsto (fun _n : ℕ ↦ quotientRowTarget)
        atTop (nhds quotientRowTarget) := tendsto_const_nhds
    simpa only [loss, limitLoss, add_zero, zero_add] using
      (((hrow.add ((hoff.add hdiag).add hsecond)).add hRT).add hnuisanceT)
  have hlimitSmall : limitLoss < quotientMain / 4 := by
    simpa only [limitLoss, Cpow] using hstructSmall
  have hlossSmall : ∀ᶠ n : ℕ in atTop, loss n < quotientMain / 2 :=
    hlossT.eventually (eventually_lt_nhds (by
      linarith [quotientMain_pos]))
  have hAnchorEvent :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
      M hdelta W hWanchor anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hReciprocal := PrimeSums.eventually_bandReciprocalSum_le_logL W
  have hLogL : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Scale.L n) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop 0)
  filter_upwards [hlossSmall, hAnchorEvent, hrowEvent, hReciprocal,
      hLogL, hcombinedNonneg, eventually_ge_atTop Nprofile,
      eventually_ge_atTop Npower, eventually_ge_atTop Nmarked] with
      n hlossN hAnchorN hRowN hReciprocalN hLogLN hcombinedN
      hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline z hz
  subst n
  subst W
  obtain ⟨hWneAnchor, hnAnchor, hAnchorAll⟩ := hAnchorN
  obtain ⟨hWneUser, S, hpartitionUser⟩ := hpartition
  let Pcanonical := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hnAnchor hWneAnchor S
  let anchor := RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet
    M Pcanonical anchors
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hinterior, hAnchorMass⟩ := hAnchorAll S
  have hinterior' : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8) := by
    simpa only [anchor, Pcanonical] using hinterior
  have hAnchorMass' : (1 / 8 : ℝ) ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchor, Pcanonical] using hAnchorMass
  have hmass : 0 < anchorMass (primeWeight B.sampleData.n)
      anchor := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hAnchorMass'
  have hPattern : B.sampleData.pattern = Phead := by
    rw [hcanonical]
    rfl
  have hLo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hHi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hGuards : B.sampleData.guards =
      (ledger B.sampleData.n).guards := by
    rw [hcanonical]
    rfl
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize xi ≤ Acoef := by
    dsimp only [xi, Acoef]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  have heffective := B.effective_bounds_of_paperEffectiveSize xi hsize
  have heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef := heffective.1
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤ Acoef := heffective.2
  have hphys : |xi MomentCoord.physical| ≤ Aphys := by
    calc
      |xi MomentCoord.physical| =
          ‖B.nuisanceParameter xi NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter xi‖ :=
        PiLp.norm_apply_le (B.nuisanceParameter xi) NuisanceCoord.physical
      _ ≤ Aphys := by simpa only [Aphys, Acoef] using hnuisance
  obtain ⟨hpair, hsingle⟩ :=
    hprofile B xi hnProfile hPattern hLo hHi hGuards heta hphys rfl
  have hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p.1 r.1 -
          (B.actualValuationLaw xi).covII p.1 r.1| ≤ R B.sampleData.n := by
    intro p
    have hraw := hpower B xi hnPower rfl hsep hremaining hcanonical
      heta hphys p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using hraw
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        quotientRowTarget * tPrime B.sampleData.n p.1 := hRowN
  have hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel := by
    intro p hp
    have ht : tPrime B.sampleData.n p ∈ Icc (0 : ℝ) 1 := by
      exact ⟨PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one hp,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one hp⟩
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelStructural _ ht _ ht
      _ ≤ CKernel * 1 :=
        mul_le_mul_of_nonneg_left ht.2 hCKernel
      _ = CKernel := by ring
  have hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
      reciprocalWeight p) ≤ H B.sampleData.n := by
    have hattach :
        (∑ p : BandPrime B.sampleData.n B.sampleData.W,
            1 / (p.1 : ℝ)) =
          ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
            1 / (p : ℝ) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ 1 / (p : ℝ)))
    unfold reciprocalWeight
    rw [hattach]
    simpa only [PrimeSums.bandReciprocalSum, H] using hReciprocalN
  have hInvW : (1 / (B.sampleData.W : ℝ)) ≤
      (1 / (B.sampleData.W : ℝ)) := le_rfl
  let gamma := B.canonicalEffectiveNuisanceGamma
    I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    simpa only [gamma, xi] using
      B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hLo hHi T hbaseline hBWlarge z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have hcard : (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ dcard := by
    dsimp only [dcard]
    exact_mod_cast B.nuisanceCoord_card_le_head_add_one
  have hH0 : 0 ≤ H B.sampleData.n := by
    dsimp only [H]
    positivity
  have hnuisanceCompare :
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma ≤
        nuisanceMajorant B.sampleData.n := by
    have hnum :
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              markedError B.sampleData.n ^ 2 * H B.sampleData.n ≤
          dcard * markedError B.sampleData.n ^ 2 * H B.sampleData.n := by
      gcongr
    exact (div_le_div₀
      (mul_nonneg (mul_nonneg hdcard (sq_nonneg _)) hH0)
      hnum hgammaFloor hgammaFloorLe : _)
  have hlossActual :
      quotientRowTarget +
          ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
              H B.sampleData.n +
            2 * profileError B.sampleData.n +
            ((1 / DickmanBasic.rho DickmanBasic.U +
                2 * profileError B.sampleData.n) ^ 2 + CKernel) *
              (1 / (B.sampleData.W : ℝ))) +
          R B.sampleData.n +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) ≤
        quotientMain / 2 := by
    have hsigned :
        ((1 / DickmanBasic.rho DickmanBasic.U +
              2 * profileError B.sampleData.n) ^ 2 + CKernel) =
          signedSecondConstant (profileError B.sampleData.n) CKernel := by
      rfl
    rw [hsigned]
    have hle :
        quotientRowTarget +
            ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
                H B.sampleData.n +
              2 * profileError B.sampleData.n +
              signedSecondConstant (profileError B.sampleData.n) CKernel *
                (1 / (B.sampleData.W : ℝ))) +
            R B.sampleData.n +
            ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) ≤
          loss B.sampleData.n := by
      dsimp only [loss]
      linarith
    exact hle.trans hlossN.le
  have hsmall :
      quotientRowTarget +
          ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
              H B.sampleData.n +
            2 * profileError B.sampleData.n +
            ((1 / DickmanBasic.rho DickmanBasic.U +
                2 * profileError B.sampleData.n) ^ 2 + CKernel) *
              (1 / (B.sampleData.W : ℝ))) +
          R B.sampleData.n +
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor := by
    calc
      _ ≤ quotientMain / 2 := hlossActual
      _ ≤ quotientMain := by linarith [quotientMain_pos]
      _ = (canonicalSlowKappa / 2) * (1 / 8 : ℝ) := by
        unfold quotientMain
        ring
      _ ≤ (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor :=
        mul_le_mul_of_nonneg_left hAnchorMass'
          (div_nonneg canonicalSlowKappa_pos.le (by norm_num))
  have hheadActual : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W := by
    intro h p
    rw [hPattern]
    exact hhead h p
  have hbase :=
    B.actualResidualSchur_fullQuotient_Dgap_canonicalKappa_independent_mu
      xi hgamma (hmarked0 B.sampleData.n) hgap hheadActual anchor hinterior'
      hmass
      (hprofile0 B.sampleData.n) hCKernel
      (by exact_mod_cast (show 0 < B.sampleData.W by omega))
      hTotal hInvW hrowReference hpair hsingle hKernel hrowPower
      hmarkedRows hsmall
  dsimp only
  intro b mu
  have hraw := hbase b mu
  dsimp only at hraw ⊢
  have hcoefficient : quotientKappa ≤
      (canonicalSlowKappa / 2) *
            anchorMass (primeWeight B.sampleData.n) anchor -
          quotientRowTarget -
          ((4 * pairCovarianceScale (profileError B.sampleData.n)) *
              H B.sampleData.n +
            2 * profileError B.sampleData.n +
            ((1 / DickmanBasic.rho DickmanBasic.U +
                2 * profileError B.sampleData.n) ^ 2 + CKernel) *
              (1 / (B.sampleData.W : ℝ))) -
          R B.sampleData.n -
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            markedError B.sampleData.n ^ 2 * H B.sampleData.n / gamma) := by
    have hmainLower : quotientMain ≤
        (canonicalSlowKappa / 2) *
          anchorMass (primeWeight B.sampleData.n) anchor := by
      calc
        quotientMain = (canonicalSlowKappa / 2) * (1 / 8 : ℝ) := by
          unfold quotientMain
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hAnchorMass'
          (div_nonneg canonicalSlowKappa_pos.le (by norm_num))
    dsimp only [quotientKappa]
    linarith
  have hnorm0 : 0 ≤ B.partition.data.bandNormSq
      (B.partition.data.gaugePart b) := B.partition.data.bandNormSq_nonneg _
  exact (mul_le_mul_of_nonneg_right hcoefficient hnorm0).trans hraw

end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal003_003.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_structural_cutoff_eventually_canonical_actualFullQuotient
