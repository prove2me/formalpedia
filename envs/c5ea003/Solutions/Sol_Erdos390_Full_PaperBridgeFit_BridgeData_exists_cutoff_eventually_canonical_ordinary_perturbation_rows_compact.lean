-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_ordinary_perturbation_rows_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:15:58.615363+00:00
-- url     : https://prove2.me/submissions/505fa1db-b289-4543-8adf-502d8a565567

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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_bandSquarefreeRegression_sub_reference_marked_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_actualWeightedRow_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
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





























































































theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]



































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





/-- The profile covariance error keeps the same moving-low rate as the
underlying one- and two-divisor profile. -/
theorem tendsto_pairCovarianceScale_mul_logL_zero
    (E : ℕ → ℝ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hERate : Filter.Tendsto
      (fun n : ℕ ↦ E n * Real.log (Scale.L n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ PaperPrimePowerChamberError.pairCovarianceScale (E n) *
        Real.log (Scale.L n)) Filter.atTop (nhds 0) := by
  have hSqRate : Filter.Tendsto
      (fun n : ℕ ↦ E n ^ 2 * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw := hE.mul hERate
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ E n * (E n * Real.log (Scale.L n)))
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    ring
  let a : ℝ := 1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)
  have hlin : Filter.Tendsto
      (fun n : ℕ ↦ a * (E n * Real.log (Scale.L n)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hERate : Filter.Tendsto
        (fun n : ℕ ↦ a * (E n * Real.log (Scale.L n)))
          Filter.atTop (nhds (a * 0)))
  have hsum := hlin.add hSqRate
  have hzero : Filter.Tendsto
      (fun n : ℕ ↦
        a * (E n * Real.log (Scale.L n)) +
          E n ^ 2 * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  apply hzero.congr'
  filter_upwards with n
  unfold PaperPrimePowerChamberError.pairCovarianceScale
  dsimp only [a]
  ring

/-- A profile with `E log L → 0` produces a vanishing moving-low row term.
The only surviving term is the explicit diagonal `1/W` correction, which is
selected before the ambient limit. -/
theorem tendsto_squarefreeSharpProfileRemainder
    (E : ℕ → ℝ) (Calpha K CKernel : ℝ) (W : ℕ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hERate : Filter.Tendsto
      (fun n : ℕ ↦ E n * Real.log (Scale.L n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (squarefreeSharpProfileRemainder E Calpha K CKernel W)
      Filter.atTop
      (nhds (((1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel) *
        (1 / (W : ℝ)))) := by
  have hcovRate := tendsto_pairCovarianceScale_mul_logL_zero E hE hERate
  have hmoving : Filter.Tendsto
      (fun n : ℕ ↦
        (4 * PaperPrimePowerChamberError.pairCovarianceScale (E n)) * K *
          (Calpha * Real.log (Scale.L n)))
        Filter.atTop (nhds 0) := by
    let c : ℝ := 4 * K * Calpha
    have hraw : Filter.Tendsto
        (fun n : ℕ ↦ c *
          (PaperPrimePowerChamberError.pairCovarianceScale (E n) *
            Real.log (Scale.L n))) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcovRate : Filter.Tendsto
          (fun n : ℕ ↦ c *
            (PaperPrimePowerChamberError.pairCovarianceScale (E n) *
              Real.log (Scale.L n))) Filter.atTop (nhds (c * 0)))
    apply hraw.congr'
    filter_upwards with n
    dsimp only [c]
    ring
  have hlinear : Filter.Tendsto (fun n : ℕ ↦ 2 * E n)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hE : Filter.Tendsto
        (fun n : ℕ ↦ (2 : ℝ) * E n) Filter.atTop (nhds (2 * 0)))
  let a : ℝ := 1 / DickmanBasic.rho DickmanBasic.U
  have hinside : Filter.Tendsto (fun n : ℕ ↦ a + 2 * E n)
      Filter.atTop (nhds a) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlinear
  have hlast : Filter.Tendsto
      (fun n : ℕ ↦ ((a + 2 * E n) ^ 2 + CKernel) * (1 / (W : ℝ)))
      Filter.atTop (nhds ((a ^ 2 + CKernel) * (1 / (W : ℝ)))) := by
    exact (hinside.pow 2 |>.add tendsto_const_nhds).mul tendsto_const_nhds
  have hsum := (hmoving.add hlinear).add hlast
  simpa only [squarefreeSharpProfileRemainder, a, zero_add] using hsum





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

/- Source module: Erdos390.Full.PaperActualFullBandIdentification -/
section


/-!
# Exact identification of the actual full-valuation band operator

The full-valuation sharp operator produced by Lemmas 7.5 and 8.4 is defined
through the bounded valuation law.  The nonlinear bridge is written through
covariance rows of the actual tilted sample.  This file proves that these
are the same finite operator before nuisance regression, and records the
exact sharp/raw gauge conjugacy.  No asymptotic estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- Exact finite nuisance-Schur correction.  The correction is displayed as
the projected normalized row of the actual regression coefficient; it is not
discarded as a generic `o(1)` perturbation. -/
theorem actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    B.actualBandSchurLinearMap xi hgamma hgap q =
      B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (B.normalizedBandCovarianceRow xi
            (fun m ↦ inner ℝ
              (B.nuisanceCoefficientOfScore xi hgamma hgap
                (B.bandRegressionScore q))
              (B.nuisanceStatistic m))) := by
  change B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))) =
    B.projectRawBandVector
        (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q)) -
      B.projectRawBandVector
        (B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore q))
            (B.nuisanceStatistic m)))
  unfold nuisanceResidualScore
  rw [B.normalizedBandCovarianceRow_sub]
  exact B.projectRawBandVector_sub _ _



















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

/-- Euclidean vector form of the preceding one-band summation. -/
theorem nuisanceCovarianceVector_bandScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (i : Band)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.harmonicMass i) := by
  have hK : 0 ≤ Cmarked * B.harmonicMass i :=
    mul_nonneg hCmarked (B.harmonicMass_pos i).le
  exact B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandScore i) hK (fun c ↦
      B.abs_covariance_nuisance_bandScore_le_of_marked
        xi c i (fun p ↦ hmarked c p))















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



















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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







theorem tPrime_mem_unit (hn : 1 < n) (p : PrimeIndex n W) :
    tPrime n p.1 ∈ Icc (0 : ℝ) 1 :=
  ⟨(tPrime_pos hn p).le,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn p.2⟩





















end Erdos390.Full.PrimeSquarefreeDirichletGeometry

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

/- Source module: Erdos390.Full.PaperActualFastMarkedRowProfiles -/
section


/-!
# Ordinary-fast marked rows from the literal analytic inputs

The fast solve is bounded in the ordinary raw-band norm.  Its reference
kernel row is nevertheless `O(1/p)`: the product bound for the Dickman
kernel supplies the missing factor `t_r`, whose prime sum is bounded.  Only
the signed profile error pays the full harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` bookkeeping.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem bandRegression_markedRows_eq_sums [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covVV p r.1 ∧
    (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p r.1 := by
  constructor
  · have hscore : B.bandRegressionScore q =
        fun m ↦ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          q.1 (B.partition.band r) *
            valuation r.1 (B.sampleData.value m) := by
      funext m
      exact B.bandRegressionScore_eq_primeSum q m
    rw [hscore]
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl
  · unfold bandSquarefreeRegressionScore
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl

/-- The full-versus-squarefree weighted row applies to an ordinary raw-band
coefficient without any moving-centre loss. -/
theorem bandRegression_full_sub_squarefree_marked_le_of_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) {R : ℝ}
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) -
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q)| ≤
      ‖q‖ * R * (1 / (p : ℝ)) := by
  rw [(B.bandRegression_markedRows_eq_sums xi q p).1,
    (B.bandRegression_markedRows_eq_sums xi q p).2]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hrowp := hrow ⟨p, hp⟩
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covVV p r.1 -
          q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covII p r.1)| =
      |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          ((B.actualValuationLaw xi).covVV p r.1 -
            (B.actualValuationLaw xi).covII p r.1)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |(B.actualValuationLaw xi).covVV p r.1 -
            (B.actualValuationLaw xi).covII p r.1| := by
      calc
        _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |q.1 (B.partition.band r) *
              ((B.actualValuationLaw xi).covVV p r.1 -
                (B.actualValuationLaw xi).covII p r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ * |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1| := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm q.1 (B.partition.band r))) (abs_nonneg _)
    _ = ‖q‖ * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1| := by rw [Finset.mul_sum]
    _ ≤ ‖q‖ * (R / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      exact (le_div_iff₀ hpR).2 (by simpa only [mul_comm] using hrowp)
    _ = ‖q‖ * R * (1 / (p : ℝ)) := by ring







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullOrdinaryRowTransfer -/
section


/-!
# Ordinary raw-row transfer to the actual full band operator

The sharp transfer divides an output row by its band centre.  The fast
solve instead uses an ordinary raw coefficient, so the prime rows are first
averaged with their exact harmonic mass.  The factor `1/p` then cancels that
mass and no moving-centre loss occurs.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerSharpBandTransfer
open SquarefreeSharpBandTransfer
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Averaging a reciprocal prime-row estimate over one exact band removes
the output reciprocal weight. -/
private theorem abs_normalized_fiber_sum_le
    {E : ℝ} (i : Band)
    (f : BandPrime B.sampleData.n B.sampleData.W → ℝ)
    (hf : ∀ p, |f p| ≤ E * (1 / (p.1 : ℝ))) :
    |(1 / B.harmonicMass i) *
        ∑ p ∈ B.partition.data.fiber i, f p| ≤ E := by
  have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
  have hsum :
      |∑ p ∈ B.partition.data.fiber i, f p| ≤
        E * B.harmonicMass i := by
    calc
      |∑ p ∈ B.partition.data.fiber i, f p| ≤
          ∑ p ∈ B.partition.data.fiber i, |f p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ B.partition.data.fiber i,
          E * (1 / (p.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hf p
      _ = E * B.harmonicMass i := by
        rw [← Finset.mul_sum]
        rfl
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hH)]
  calc
    (1 / B.harmonicMass i) *
        |∑ p ∈ B.partition.data.fiber i, f p| ≤
      (1 / B.harmonicMass i) * (E * B.harmonicMass i) :=
        mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hH.le)
    _ = E := by field_simp [hH.ne']

/-- The signed squarefree profile comparison in an ordinary raw band row.
The off-diagonal error pays the total harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` estimate. -/
theorem squarefreeBandRow_sub_referenceBandRow_le_ordinary
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond H : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonSecond : 0 ≤ epsilonSecond)
    (hW : 0 < B.sampleData.W)
    (hH : ∑ j : Band, B.harmonicMass j ≤ H)
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
    (i : Band) :
    |squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤
      ‖q‖ * (epsilonOff * H + epsilonDiag +
        epsilonSecond * (1 / (B.sampleData.W : ℝ))) := by
  let E : ℝ := ‖q‖ * (epsilonOff * H + epsilonDiag +
    epsilonSecond * (1 / (B.sampleData.W : ℝ)))
  let f : BandPrime B.sampleData.n B.sampleData.W → ℝ := fun p ↦
    (∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p.1 r.1) -
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p.1 r.1
  have hf (p : BandPrime B.sampleData.n B.sampleData.W) :
      |f p| ≤ E * (1 / (p.1 : ℝ)) := by
    have hp := B.bandSquarefreeRegression_sub_reference_marked_le
      xi q hepsilonOff hH hentry p.2
    rw [(B.bandRegression_markedRows_eq_sums xi q p.1).2] at hp
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hWR : (0 : ℝ) < B.sampleData.W := by exact_mod_cast hW
    have hWp : (B.sampleData.W : ℝ) ≤ p.1 := by
      exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le
    have hinv : 1 / (p.1 : ℝ) ≤ 1 / (B.sampleData.W : ℝ) :=
      one_div_le_one_div_of_le hWR hWp
    have hcoef :
        epsilonOff * H + epsilonDiag +
            epsilonSecond * (1 / (p.1 : ℝ)) ≤
          epsilonOff * H + epsilonDiag +
            epsilonSecond * (1 / (B.sampleData.W : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv hepsilonSecond)
    have hscaled :
        ‖q‖ * (epsilonOff * H + epsilonDiag +
              epsilonSecond * (1 / (p.1 : ℝ))) * (1 / (p.1 : ℝ)) ≤
          E * (1 / (p.1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hpPos.le)
      exact mul_le_mul_of_nonneg_left hcoef (norm_nonneg q)
    exact hp.trans (by simpa only [E] using hscaled)
  have havg := B.abs_normalized_fiber_sum_le i f hf
  unfold squarefreeBandRow referenceBandRow
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simpa only [f, E] using havg

/-- Lemma 7.5's weighted full-versus-squarefree row also transfers to an
ordinary raw band coefficient without a least-centre divisor. -/
theorem fullBandRow_sub_squarefreeBandRow_le_ordinary
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) {R : ℝ}
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (i : Band) :
    |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow (B.actualValuationLaw xi) B.partition q.1 i| ≤
      ‖q‖ * R := by
  let E : ℝ := ‖q‖ * R
  let f : BandPrime B.sampleData.n B.sampleData.W → ℝ := fun p ↦
    (∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covVV p.1 r.1) -
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p.1 r.1
  have hf (p : BandPrime B.sampleData.n B.sampleData.W) :
      |f p| ≤ E * (1 / (p.1 : ℝ)) := by
    have hp := B.bandRegression_full_sub_squarefree_marked_le_of_weightedRow
      xi q hrow p.2
    rw [(B.bandRegression_markedRows_eq_sums xi q p.1).1,
      (B.bandRegression_markedRows_eq_sums xi q p.1).2] at hp
    simpa only [f, E] using hp
  have havg := B.abs_normalized_fiber_sum_le i f hf
  unfold fullBandRow squarefreeBandRow
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simpa only [f, E] using havg



end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurOrdinaryRow -/
section


/-!
# Ordinary raw-norm nuisance--Schur transfer

The sharp Schur estimate divides by the least band centre.  That loss is
appropriate for a sharp input, but it is spurious for the ordinary raw
supremum norm required by the fast solve.  Here both prime-band summations
are performed before projection.  The result depends on the total harmonic
mass, which is later paired with the genuinely vanishing marked rate; it has
no factor `1 / min alpha`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open OrdinaryRawInverseTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Two covariance-vector estimates give an ordinary raw row bound for the
literal nuisance correction.  The projection loss is expressed only by the
displayed first-moment/centre-energy ratio. -/
theorem actualBandSchur_sub_full_norm_le_of_nuisanceCovarianceBounds_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Csource Crow R : ℝ}
    (hCsource : 0 ≤ Csource) (hCrow : 0 ≤ Crow) (hR : 0 ≤ R)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hsource : ∀ q : B.RawBandGauge,
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ≤
        Csource * ‖q‖)
    (hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i)
    (q : B.RawBandGauge) :
    ‖B.actualBandSchurLinearMap xi hgamma hgap q -
        B.actualBandFullLinearMap xi q‖ ≤
      ((1 + R) * ((Csource / gamma) * Crow)) * ‖q‖ := by
  let A : ℝ := (Csource / gamma) * Crow
  let z : EuclideanSpace ℝ (NuisanceCoord B.HeadIndex) :=
    B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.bandRegressionScore q)
  let correction : Band → ℝ := fun i ↦
    B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) i
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (div_nonneg hCsource hgamma.le) hCrow
  have hz : ‖z‖ ≤ (Csource / gamma) * ‖q‖ := by
    calc
      ‖z‖ ≤
          ‖B.nuisanceCovarianceVector xi
            (B.bandRegressionScore q)‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
      _ ≤ (Csource * ‖q‖) / gamma :=
        div_le_div_of_nonneg_right (hsource q) hgamma.le
      _ = (Csource / gamma) * ‖q‖ := by ring
  have hcorrection : ∀ i : Band, |correction i| ≤ A * ‖q‖ := by
    intro i
    have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
    change |B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) i| ≤ _
    unfold normalizedBandCovarianceRow
    rw [B.covariance_marked_nuisanceScore_eq_inner,
      abs_div, abs_of_pos hH]
    have hinner := abs_real_inner_le_norm z
      (B.nuisanceCovarianceVector xi (B.bandScore i))
    calc
      |inner ℝ z (B.nuisanceCovarianceVector xi (B.bandScore i))| /
          B.harmonicMass i ≤
        (‖z‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
          B.harmonicMass i :=
        div_le_div_of_nonneg_right hinner hH.le
      _ ≤ (((Csource / gamma) * ‖q‖) *
          (Crow * B.harmonicMass i)) / B.harmonicMass i := by
        apply div_le_div_of_nonneg_right _ hH.le
        exact mul_le_mul hz (hband i) (norm_nonneg _)
          (mul_nonneg (div_nonneg hCsource hgamma.le) (norm_nonneg q))
      _ = A * ‖q‖ := by
        dsimp only [A]
        field_simp [ne_of_gt hH]
  have hproject :
      ‖B.projectRawBandVector correction‖ ≤
        (1 + R) * (A * ‖q‖) :=
    B.projectRawBandVector_norm_le_of_moment_ratio
      correction (mul_nonneg hA (norm_nonneg q)) hR hcorrection hRatio
  rw [B.actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    xi hgamma hgap q]
  simpa only [sub_sub_cancel_left, norm_neg, correction, z, A,
    mul_assoc] using hproject



/-- The reciprocal marked-prime family closes the ordinary nuisance row
without using a lower bound for the moving centre. -/
theorem actualBandSchur_sub_full_norm_le_of_marked_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Cmarked R : ℝ} (hCmarked : 0 ≤ Cmarked) (hR : 0 ≤ R)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      R * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : B.RawBandGauge) :
    ‖B.actualBandSchurLinearMap xi hgamma hgap q -
        B.actualBandFullLinearMap xi q‖ ≤
      B.nuisanceMarkedOrdinarySchurRate Cmarked gamma R * ‖q‖ := by
  let droot : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let totalMass : ℝ := ∑ j : Band, B.harmonicMass j
  let Csource : ℝ := droot * (Cmarked * totalMass)
  let Crow : ℝ := droot * Cmarked
  have htotalMass : 0 ≤ totalMass := by
    dsimp only [totalMass]
    exact Finset.sum_nonneg fun j _ ↦ (B.harmonicMass_pos j).le
  have hdroot : 0 ≤ droot := Real.sqrt_nonneg _
  have hCsource : 0 ≤ Csource :=
    mul_nonneg hdroot (mul_nonneg hCmarked htotalMass)
  have hCrow : 0 ≤ Crow := mul_nonneg hdroot hCmarked
  have hsource : ∀ q' : B.RawBandGauge,
      ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q')‖ ≤
        Csource * ‖q'‖ := by
    intro q'
    have h := B.nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
      xi hCmarked hmarked q'
    simpa only [Csource, droot, totalMass, mul_assoc] using h
  have hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i := by
    intro i
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [Crow, droot, mul_assoc] using h
  have h := B.actualBandSchur_sub_full_norm_le_of_nuisanceCovarianceBounds_ordinary
    xi hgamma hgap hCsource hCrow hR hRatio hsource hband q
  simpa only [nuisanceMarkedOrdinarySchurRate, Csource, Crow,
    droot, totalMass] using h



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

/- Source module: Erdos390.Full.PaperCanonicalActualSchurOrdinaryRowsEventually -/
section


/-!
# Fully discharged ordinary perturbation rows for Lemma 8.4

This file packages the three analytic perturbations used by the endpoint
ordinary inverse: squarefree-to-reference, full-to-squarefree, and the
nuisance Schur correction.  The fixed `1/W` tails are made small before the
head data and the effective tilt ball are selected.  Every dependence on the
later ball is confined to an eventual error in the ambient parameter `n`.

The only local premise retained by the last row is the exact first-moment to
centre-energy ratio.  That geometric premise is supplied, without analytic
assumptions, by the separate canonical moment-ratio terminal when the final
Lemma 8.4 wrapper is assembled.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open SquarefreeCovarianceReference
open PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry

namespace BridgeData





theorem canonicalOrdinaryRowTolerance_pos
    {Cref Rproj : ℝ} (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    0 < canonicalOrdinaryRowTolerance Cref Rproj := by
  unfold canonicalOrdinaryRowTolerance
  positivity

theorem canonicalOrdinarySchurTolerance_pos
    {Cref : ℝ} (hCref : 0 < Cref) :
    0 < canonicalOrdinarySchurTolerance Cref := by
  unfold canonicalOrdinarySchurTolerance
  positivity





/-- A product-log rate and eventual nonnegativity imply ordinary
convergence. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilon : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n)
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
    filter_upwards [hepsilon, hlogOne] with n hn hlog
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hn
  exact squeeze_zero' hepsilon hupper hrate

/-- The literal ordinary nuisance rate is bounded by a scalar majorant once
the total harmonic mass and the nuisance gap have uniform bounds. -/
theorem nuisanceMarkedOrdinarySchurRate_le_majorant
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {Cmarked gamma gammaFloor R H : ℝ}
    (hCmarked : 0 ≤ Cmarked) (hgammaFloor : 0 < gammaFloor)
    (hgammaFloorLe : gammaFloor ≤ gamma)
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hmass : (∑ j : Band, B.harmonicMass j) ≤ H) :
    B.nuisanceMarkedOrdinarySchurRate Cmarked gamma R ≤
      (1 + R) *
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * H)) / gammaFloor) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) := by
  have hgamma : 0 < gamma := hgammaFloor.trans_le hgammaFloorLe
  have hdroot : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sqrt_nonneg _
  have hmass0 : 0 ≤ ∑ j : Band, B.harmonicMass j :=
    Finset.sum_nonneg fun j hj ↦ (B.harmonicMass_pos j).le
  unfold nuisanceMarkedOrdinarySchurRate
  dsimp only
  have hsource :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * ∑ j : Band, B.harmonicMass j) ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * H) := by
    gcongr
  have hnum0 : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * H) := by positivity
  have hdiv :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * ∑ j : Band, B.harmonicMass j)) / gamma ≤
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * H)) / gammaFloor := by
    exact (div_le_div₀ hnum0 hsource hgammaFloor hgammaFloorLe : _)
  gcongr

set_option maxHeartbeats 3000000 in
/--
All three ordinary perturbation rows, with every analytic error discharged.

`Cref` and `Rproj` are fixed before `W`.  The cutoff is then fixed before the
head patterns and the effective ball.  The conclusion is uniform over that
whole ball and over every canonical bridge at the displayed `n,W`.
-/
theorem exists_cutoff_eventually_canonical_ordinary_perturbation_rows
    (Cref Rproj : ℝ) (hCref : 0 < Cref) (hRproj : 0 ≤ Rproj) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p ∈ (Phead h).primes, p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band],
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
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ((∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤
                Rproj * MovingLowGaugeTransfer.sharpWeightTotal
                  B.harmonicMass B.bandCenter) →
              ( (∀ (z : B.EffectiveParamSpace)
                    (_hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ))
                    (q : B.RawBandGauge) (i : Band),
                  |SquarefreeSharpBandTransfer.squarefreeBandRow
                      (B.actualValuationLaw (B.effectiveParamEquiv z))
                        B.partition q.1 i -
                    SquarefreeSharpBandTransfer.referenceBandRow
                      B.partition q.1 i| ≤
                    ‖q‖ * canonicalOrdinaryRowTolerance Cref Rproj) ∧
                (∀ (z : B.EffectiveParamSpace)
                    (_hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ))
                    (q : B.RawBandGauge) (i : Band),
                  |PrimePowerSharpBandTransfer.fullBandRow
                      (B.actualValuationLaw (B.effectiveParamEquiv z))
                        B.partition q.1 i -
                    SquarefreeSharpBandTransfer.squarefreeBandRow
                      (B.actualValuationLaw (B.effectiveParamEquiv z))
                        B.partition q.1 i| ≤
                    ‖q‖ * canonicalOrdinaryRowTolerance Cref Rproj) ∧
                ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ))
                    (q : B.RawBandGauge),
                  ‖B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU (by
                            intro sigma; rw [hcanonical]; rfl) (by
                            intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q -
                      B.actualBandFullLinearMap
                        (B.effectiveParamEquiv z) q‖ ≤
                    canonicalOrdinarySchurTolerance Cref * ‖q‖ ) := by
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_second
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  let rowTol : ℝ := canonicalOrdinaryRowTolerance Cref Rproj
  let schurTol : ℝ := canonicalOrdinarySchurTolerance Cref
  have hrowTol : 0 < rowTol := by
    dsimp only [rowTol]
    exact canonicalOrdinaryRowTolerance_pos hCref hRproj
  have hschurTol : 0 < schurTol := by
    dsimp only [schurTol]
    exact canonicalOrdinarySchurTolerance_pos hCref
  have hInvNat : Tendsto (fun W : ℕ ↦ 1 / (W : ℝ))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hreal.comp tendsto_natCast_atTop_atTop
    simpa only [one_div] using h
  let squareTailConstant : ℝ :=
    (1 / DickmanBasic.rho DickmanBasic.U) ^ 2 + CKernel
  have hSquareTail : Tendsto (fun W : ℕ ↦
      squareTailConstant * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ squareTailConstant * (1 / (W : ℝ)))
          atTop (nhds (squareTailConstant * 0)))
  have hFullTail : Tendsto (fun W : ℕ ↦
      Cpow * (1 / (W : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hInvNat : Tendsto
        (fun W : ℕ ↦ Cpow * (1 / (W : ℝ)))
          atTop (nhds (Cpow * 0)))
  obtain ⟨Wsquare, hWsquare⟩ := eventually_atTop.1
    (hSquareTail.eventually
      (eventually_lt_nhds (half_pos hrowTol)))
  obtain ⟨Wfull, hWfull⟩ := eventually_atTop.1
    (hFullTail.eventually
      (eventually_lt_nhds (half_pos hrowTol)))
  let W₀ : ℕ := max 2 (max Wsquare Wfull)
  refine ⟨W₀, ?_⟩
  intro W hWcut Head _instHead _instHeadDec _instHeadNonempty
    Phead hHeadLe I U hU hlowerOne hupperU Cprom Cbank ledger
    a marginFloor hmarginFloor Band _instBand _instBandDec _instBandNonempty
  have hWtwo : 2 ≤ W := (le_max_left 2 _).trans hWcut
  have hWone : 1 < W := by omega
  have hWsquare' : Wsquare ≤ W := by
    exact (le_max_left Wsquare Wfull).trans
      ((le_max_right 2 _).trans hWcut)
  have hWfull' : Wfull ≤ W := by
    exact (le_max_right Wsquare Wfull).trans
      ((le_max_right 2 _).trans hWcut)
  have hSquareTailLt :
      squareTailConstant * (1 / (W : ℝ)) < rowTol / 2 :=
    hWsquare W hWsquare'
  have hFullTailLt : Cpow * (1 / (W : ℝ)) < rowTol / 2 :=
    hWfull W hWfull'
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨profileError, hprofile0, hprofileT, hprofileRate,
      Nprofile, hprofile⟩ :=
    exists_boxIndependent_actual_component_signed_profiles
      Phead I U hlowerOne hupperU Cprom Cbank ledger W hWone hHeadLe
        Acoef Aphys hAcoef hAphys
  obtain ⟨_hCpowTerminal, hpowerTerminal⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, hepsilon75T, _hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hpowerTerminal W hWone hHeadLe Acoef hAcoef Aphys hAphys
  obtain ⟨markedError, hmarked0, hmarkedRate, Nmarked, hmarked⟩ :=
    _root_.Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      Phead I U hU hlowerOne hupperU Cprom Cbank ledger W hWone
        hHeadLe a
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
  have hSquareRemainderT := tendsto_squarefreeSharpProfileRemainder
    profileError 1 12 CKernel W hprofileT hprofileRate
  have hSquareSmall : ∀ᶠ n : ℕ in atTop,
      squarefreeSharpProfileRemainder
        profileError 1 12 CKernel W n < rowTol :=
    hSquareRemainderT.eventually (eventually_lt_nhds (by
      simpa only [squareTailConstant] using
        (hSquareTailLt.trans (half_lt_self hrowTol))))
  let Rpow : ℕ → ℝ := fun n ↦
    Cpow * (1 / (W : ℝ)) + epsilon75 n + combined n
  have hRpowT : Tendsto Rpow atTop
      (nhds (Cpow * (1 / (W : ℝ)))) := by
    simpa only [Rpow, add_zero] using
      (tendsto_const_nhds.add hepsilon75T).add hcombinedT
  have hFullSmall : ∀ᶠ n : ℕ in atTop, Rpow n < rowTol :=
    hRpowT.eventually (eventually_lt_nhds (by
      exact hFullTailLt.trans (half_lt_self hrowTol)))
  have hmarkedT : Tendsto markedError atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero markedError
      (Filter.Eventually.of_forall hmarked0) hmarkedRate
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos I hmarginFloor
  let droot : ℝ := nuisanceDimensionCeiling Head
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  let H : ℕ → ℝ := fun n ↦ 12 * Real.log (Scale.L n)
  have hmarkedSquareLog : Tendsto
      (fun n : ℕ ↦ markedError n *
        (markedError n * Real.log (Scale.L n))) atTop (nhds 0) := by
    simpa only [mul_zero] using hmarkedT.mul hmarkedRate
  let nuisanceMajorant : ℕ → ℝ := fun n ↦
    (1 + Rproj) *
      (((droot * (markedError n * H n)) / gammaFloor) *
        (droot * markedError n))
  have hnuisanceT : Tendsto nuisanceMajorant atTop (nhds 0) := by
    have hcore : Tendsto (fun n : ℕ ↦
        markedError n * (markedError n * H n)) atTop (nhds 0) := by
      have hconst : Tendsto (fun _n : ℕ ↦ (12 : ℝ))
          atTop (nhds 12) := tendsto_const_nhds
      have hscaled : Tendsto (fun n : ℕ ↦
          (12 : ℝ) *
            (markedError n * (markedError n * Real.log (Scale.L n))))
          atTop (nhds 0) := by
        simpa only [mul_zero] using hconst.mul hmarkedSquareLog
      apply hscaled.congr'
      filter_upwards with n
      dsimp only [H]
      ring
    have hconst : Tendsto (fun _n : ℕ ↦
        (1 + Rproj) * (droot ^ 2 / gammaFloor))
        atTop (nhds ((1 + Rproj) * (droot ^ 2 / gammaFloor))) :=
      tendsto_const_nhds
    have hscaled : Tendsto (fun n : ℕ ↦
        ((1 + Rproj) * (droot ^ 2 / gammaFloor)) *
          (markedError n * (markedError n * H n)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hconst.mul hcore
    apply hscaled.congr'
    filter_upwards with n
    dsimp only [nuisanceMajorant]
    field_simp [hgammaFloor.ne']
  have hNuisanceSmall : ∀ᶠ n : ℕ in atTop,
      nuisanceMajorant n < schurTol :=
    hnuisanceT.eventually (eventually_lt_nhds hschurTol)
  have hmassN := eventually_sum_harmonicMass_le_twelve_logL
    (Head := Head) (Band := Band) W
  filter_upwards [hSquareSmall, hFullSmall, hNuisanceSmall, hmassN,
      eventually_ge_atTop Nprofile, eventually_ge_atTop Npower,
      eventually_ge_atTop Nmarked] with
      n hSquareN hFullN hNuisanceN hmassAt hnProfile hnPower hnMarked
  intro B hBn hBW hBWlarge hsep hremaining hcanonical
    T hTmargin hbaseline hRatio
  subst n
  subst W
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
  have hmass : (∑ j : Band, B.harmonicMass j) ≤
      H B.sampleData.n := by
    simpa only [H] using hmassAt B rfl rfl
  have hH0 : 0 ≤ H B.sampleData.n :=
    (Finset.sum_nonneg fun j hj ↦ (B.harmonicMass_pos j).le).trans hmass
  have hKernel : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
        CKernel := by
    intro p hp
    let p' : PrimeIndex B.sampleData.n B.sampleData.W := ⟨p, hp⟩
    have ht := tPrime_mem_unit B.n_gt_one p'
    calc
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
          CKernel * tPrime B.sampleData.n p :=
        hKernelBound _ ht _ ht
      _ ≤ CKernel := mul_le_of_le_one_right hCKernel ht.2
  have hEffectiveBounds : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient (B.effectiveParamEquiv z) p| ≤ Acoef) ∧
      |B.effectiveParamEquiv z MomentCoord.physical| ≤ Aphys := by
    intro z hz
    have hznorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ Acoef := by
      dsimp only [Acoef]
      exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
        (mul_le_mul_of_nonneg_left hznorm (by norm_num))
    have heffective :=
      B.effective_bounds_of_paperEffectiveSize (B.effectiveParamEquiv z) hsize
    refine ⟨heffective.1, ?_⟩
    calc
      |B.effectiveParamEquiv z MomentCoord.physical| =
          ‖B.nuisanceParameter (B.effectiveParamEquiv z)
            NuisanceCoord.physical‖ := by
        simp only [B.nuisanceParameter_physical, Real.norm_eq_abs]
      _ ≤ ‖B.nuisanceParameter (B.effectiveParamEquiv z)‖ :=
        PiLp.norm_apply_le _ _
      _ ≤ Aphys := by simpa only [Aphys, Acoef] using heffective.2
  have hSquareRows : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (q : B.RawBandGauge) (i : Band),
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw (B.effectiveParamEquiv z))
            B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * rowTol := by
    intro z hz q i
    obtain ⟨heta, hphys⟩ := hEffectiveBounds z hz
    obtain ⟨hpair, hsingle⟩ := hprofile B (B.effectiveParamEquiv z)
      hnProfile hPattern hLo hHi hGuards heta hphys rfl
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability
        (B.scaledBridgeScore (B.effectiveParamEquiv z))
    have hentryMix :=
      sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
        (hprofile0 B.sampleData.n) weight
        (B.actualComponentValuationLaw (B.effectiveParamEquiv z))
        B.n_gt_one hpair hsingle hKernel
    have hlaw :=
      B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
        (B.effectiveParamEquiv z)
    dsimp only at hentryMix hlaw
    rw [hlaw] at hentryMix
    let E : ℝ := profileError B.sampleData.n
    let eOff : ℝ := 4 * pairCovarianceScale E
    let eDiag : ℝ := 2 * E
    let cDiag : ℝ :=
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel
    have hE : 0 ≤ E := by simpa only [E] using hprofile0 B.sampleData.n
    have heOff : 0 ≤ eOff := by
      dsimp only [eOff]
      exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)
    have hcDiag : 0 ≤ cDiag := by
      dsimp only [cDiag]
      positivity
    have hentry : ∀ p r,
        p ∈ primeBand B.sampleData.n B.sampleData.W →
        r ∈ primeBand B.sampleData.n B.sampleData.W →
        |(B.actualValuationLaw (B.effectiveParamEquiv z)).covII p r -
            squarefreeReferenceEntry B.sampleData.n p r| ≤
          eOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then
              eDiag * (1 / (p : ℝ)) +
                cDiag * (1 / (p : ℝ)) ^ 2
            else 0 := by
      intro p r hp hr
      let p' : BandPrime B.sampleData.n B.sampleData.W := ⟨p, hp⟩
      let r' : BandPrime B.sampleData.n B.sampleData.W := ⟨r, hr⟩
      have hraw := hentryMix p' r'
      simpa only [p', r', E, eOff, eDiag, cDiag, div_eq_mul_inv,
        one_div, Subtype.mk.injEq, mul_inv_rev, inv_pow, mul_assoc,
        mul_left_comm, mul_comm, one_mul, mul_one] using hraw
    have hrow := B.squarefreeBandRow_sub_referenceBandRow_le_ordinary
      (B.effectiveParamEquiv z) q heOff hcDiag
      (by exact_mod_cast (show 0 < B.sampleData.W by omega))
      hmass hentry i
    have hremainder :
        eOff * H B.sampleData.n + eDiag +
            cDiag * (1 / (B.sampleData.W : ℝ)) =
          squarefreeSharpProfileRemainder
            profileError 1 12 CKernel B.sampleData.W B.sampleData.n := by
      dsimp only [eOff, eDiag, cDiag, E, H,
        squarefreeSharpProfileRemainder]
      ring
    calc
      _ ≤ ‖q‖ * (eOff * H B.sampleData.n + eDiag +
          cDiag * (1 / (B.sampleData.W : ℝ))) := hrow
      _ = ‖q‖ * squarefreeSharpProfileRemainder
          profileError 1 12 CKernel B.sampleData.W B.sampleData.n := by
        rw [hremainder]
      _ ≤ ‖q‖ * rowTol :=
        mul_le_mul_of_nonneg_left hSquareN.le (norm_nonneg q)
  have hFullRows : ∀ (z : B.EffectiveParamSpace)
      (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (q : B.RawBandGauge) (i : Band),
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw (B.effectiveParamEquiv z))
            B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw (B.effectiveParamEquiv z))
            B.partition q.1 i| ≤ ‖q‖ * rowTol := by
    intro z hz q i
    obtain ⟨heta, hphys⟩ := hEffectiveBounds z hz
    have hweighted : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
        (p.1 : ℝ) *
          ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |(B.actualValuationLaw (B.effectiveParamEquiv z)).covVV p.1 r.1 -
              (B.actualValuationLaw (B.effectiveParamEquiv z)).covII p.1 r.1| ≤
          Rpow B.sampleData.n := by
      intro p
      have hraw := hpower B (B.effectiveParamEquiv z) hnPower rfl
        hsep hremaining hcanonical heta hphys p
      simpa only [Rpow, Cpow, combined,
        canonicalCombinedPowerCorrection] using hraw
    have hrow := B.fullBandRow_sub_squarefreeBandRow_le_ordinary
      (B.effectiveParamEquiv z) q hweighted i
    exact hrow.trans
      (mul_le_mul_of_nonneg_left hFullN.le (norm_nonneg q))
  refine ⟨by simpa only [rowTol] using hSquareRows,
    by simpa only [rowTol] using hFullRows, ?_⟩
  intro z hz q
  let xi : B.ParamSpace := B.effectiveParamEquiv z
  let gamma : ℝ :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
      inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
    intro v
    dsimp only [gamma, xi]
    exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU hLo hHi T hbaseline hBWlarge z hz v
  have hgammaFloorLe : gammaFloor ≤ gamma := by
    dsimp only [gammaFloor, gamma]
    exact B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
  have hmarkedRows : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          markedError B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro c p
    dsimp only [xi]
    exact hmarked B z hz hnMarked rfl hsep hremaining hcanonical c p
  have hrow := B.actualBandSchur_sub_full_norm_le_of_marked_ordinary
    xi hgamma hgap (hmarked0 B.sampleData.n) hRproj hRatio hmarkedRows q
  have hrateExact := B.nuisanceMarkedOrdinarySchurRate_le_majorant
    (hmarked0 B.sampleData.n) hgammaFloor hgammaFloorLe hRproj hH0 hmass
  have hdrootCompare :
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
        droot := by
    simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling
  have hmajorant :
      B.nuisanceMarkedOrdinarySchurRate
          (markedError B.sampleData.n) gamma Rproj ≤
        nuisanceMajorant B.sampleData.n := by
    refine hrateExact.trans ?_
    dsimp only [nuisanceMajorant]
    have hmarkedN0 := hmarked0 B.sampleData.n
    have hleft0 : 0 ≤ 1 + Rproj := by linarith
    gcongr
  calc
    ‖B.actualBandSchurLinearMap xi hgamma hgap q -
        B.actualBandFullLinearMap xi q‖ ≤
      B.nuisanceMarkedOrdinarySchurRate
          (markedError B.sampleData.n) gamma Rproj * ‖q‖ := hrow
    _ ≤ nuisanceMajorant B.sampleData.n * ‖q‖ :=
      mul_le_mul_of_nonneg_right hmajorant (norm_nonneg q)
    _ ≤ schurTol * ‖q‖ :=
      mul_le_mul_of_nonneg_right hNuisanceN.le (norm_nonneg q)
    _ = canonicalOrdinarySchurTolerance Cref * ‖q‖ := by
      rw [show schurTol = canonicalOrdinarySchurTolerance Cref by rfl]

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal001_015.{u_1, u_2} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_ordinary_perturbation_rows
