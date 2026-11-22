-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:18:31.067934+00:00
-- url     : https://prove2.me/submissions/ac40f101-94ad-4c8c-ab96-2f72a1076a5e

import Definitions.Def_erdos390_remaining_analytic_propositions_003
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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_actualWeightedRow_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients_compact



section
universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients : Erdos390.RemainingAnalyticGoal002_004.{u_1} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients_compact
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





theorem full_sub_squarefree_eq
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    fullValuationQuadratic law S c - squarefreeQuadratic law S c =
      ∑ p ∈ S, ∑ q ∈ S,
        c p * c q * (law.covVV p q - law.covII p q) := by
  unfold fullValuationQuadratic squarefreeQuadratic
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem fullValuationQuadratic_eq_covariance
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    fullValuationQuadratic law S c =
      law.probability.covariance
        (fun omega ↦ ∑ p ∈ S, c p * law.V p omega)
        (fun omega ↦ ∑ p ∈ S, c p * law.V p omega) := by
  rw [law.probability.covariance_sum_left]
  unfold fullValuationQuadratic covVV
  apply Finset.sum_congr rfl
  intro p hp
  rw [law.probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_left,
    law.probability.covariance_smul_right]
  ring

theorem squarefreeQuadratic_eq_covariance
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    squarefreeQuadratic law S c =
      law.probability.covariance
        (fun omega ↦ ∑ p ∈ S, c p * law.I p omega)
        (fun omega ↦ ∑ p ∈ S, c p * law.I p omega) := by
  rw [law.probability.covariance_sum_left]
  unfold squarefreeQuadratic covII
  apply Finset.sum_congr rfl
  intro p hp
  rw [law.probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_left,
    law.probability.covariance_smul_right]
  ring

/-- A weighted row bound and the literal coefficient `L∞`/`L¹` bounds imply
a relative quadratic error. -/
theorem abs_full_sub_squarefree_le_of_row
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup CL1 w R : ℝ}
    (hCsup : 0 ≤ Csup) (hCL1 : 0 ≤ CL1)
    (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hcSup : ∀ p ∈ primeBand n W, |c p| ≤ Csup * w)
    (hcL1 : (∑ p ∈ primeBand n W,
      |c p| * (1 / (p : ℝ))) ≤ CL1 * w)
    (hrow : ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤ R) :
    |fullValuationQuadratic law (primeBand n W) c -
        squarefreeQuadratic law (primeBand n W) c| ≤
      (Csup * CL1) * R * w ^ 2 := by
  have hCw : 0 ≤ Csup * w := mul_nonneg hCsup hw
  have hLw : 0 ≤ CL1 * w := mul_nonneg hCL1 hw
  rw [full_sub_squarefree_eq]
  calc
    |∑ p ∈ primeBand n W, ∑ q ∈ primeBand n W,
        c p * c q * (law.covVV p q - law.covII p q)| ≤
        ∑ p ∈ primeBand n W,
          |∑ q ∈ primeBand n W,
            c p * c q * (law.covVV p q - law.covII p q)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primeBand n W,
        |c p| * (Csup * w) *
          (∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q|) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        |∑ q ∈ primeBand n W,
            c p * c q * (law.covVV p q - law.covII p q)| ≤
            ∑ q ∈ primeBand n W,
              |c p * c q * (law.covVV p q - law.covII p q)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ q ∈ primeBand n W,
            |c p| * |c q| *
              |law.covVV p q - law.covII p q| := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [abs_mul, abs_mul]
        _ ≤ ∑ q ∈ primeBand n W,
            |c p| * (Csup * w) *
              |law.covVV p q - law.covII p q| := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcSup q hq) (abs_nonneg _))
            (abs_nonneg _)
        _ = |c p| * (Csup * w) *
            (∑ q ∈ primeBand n W,
              |law.covVV p q - law.covII p q|) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ primeBand n W,
        (|c p| * (1 / (p : ℝ))) * (Csup * w) * R := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPosNat : 0 < p := (prime_of_mem_primeBand hp).pos
      have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPosNat
      have hrowDiv :
          (∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q|) ≤ R / (p : ℝ) := by
        exact (le_div_iff₀ hpPos).2 (by
          simpa only [mul_comm] using hrow p hp)
      have hmult : 0 ≤ |c p| * (Csup * w) :=
        mul_nonneg (abs_nonneg _) hCw
      calc
        |c p| * (Csup * w) *
            (∑ q ∈ primeBand n W,
              |law.covVV p q - law.covII p q|) ≤
            |c p| * (Csup * w) * (R / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hrowDiv hmult
        _ = (|c p| * (1 / (p : ℝ))) * (Csup * w) * R := by
          field_simp [ne_of_gt hpPos]
    _ = (Csup * w) * R *
        (∑ p ∈ primeBand n W, |c p| * (1 / (p : ℝ))) := by
      rw [← Finset.sum_mul]
      have hfactor :
          (∑ p ∈ primeBand n W,
            |c p| * (1 / (p : ℝ)) * (Csup * w)) =
          (Csup * w) *
            ∑ p ∈ primeBand n W, |c p| * (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hfactor]
      ring
    _ ≤ (Csup * w) * R * (CL1 * w) := by
      exact mul_le_mul_of_nonneg_left hcL1
        (mul_nonneg hCw hR)
    _ = (Csup * CL1) * R * w ^ 2 := by ring













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



/-- Exact identification of the two finite covariance quadratic forms with
the actual full-valuation and squarefree scores. -/
theorem actualQuadratics_eq_covariances [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    fullValuationQuadratic (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) =
      (B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) ∧
    squarefreeQuadratic (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) =
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  constructor
  · rw [fullValuationQuadratic_eq_covariance]
    congr 1 <;> funext m <;>
      exact (B.postBandPrimeScore_eq_actualValuationSum xi q m).symm
  · rw [squarefreeQuadratic_eq_covariance]
    rfl







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



/-- Relative compensated slow-quadratic transfer from a literal actual-law
weighted row.  No other field of Lemma 7.5 is used. -/
theorem actual_primePower_relative_variance_bound_of_row
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R) :
    |(B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)| ≤
      ((1 + C) * (7 + C * K)) * R * w ^ 2 := by
  have hthree :=
    B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hcSup := hthree.1
  have hcL1 := hthree.2.1
  have hnatSup : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q p| ≤ (1 + C) * w := by
    intro p hp
    rw [B.actualCompensatedNatCoefficient_of_mem q hp]
    rw [← B.partition_compensatedCoefficient_eq q ⟨p, hp⟩]
    exact hcSup ⟨p, hp⟩
  have hnatL1 :
      (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ))) ≤
        (7 + C * K) * w := by
    rw [B.compensatedNatL1_eq_partition]
    exact hcL1
  have hrowNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      (p : ℝ) * ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p r -
          (B.actualValuationLaw xi).covII p r| ≤ R := by
    intro p hp
    have hrowSubtype := hrow ⟨p, hp⟩
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun r ↦ |(B.actualValuationLaw xi).covVV p r -
        (B.actualValuationLaw xi).covII p r|)
    change (p : ℝ) *
      (∑ r ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1|) ≤ R at hrowSubtype
    rw [hattach] at hrowSubtype
    simpa only using hrowSubtype
  have hquad := abs_full_sub_squarefree_le_of_row
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    (show 0 ≤ 1 + C by linarith)
    (show 0 ≤ 7 + C * K by positivity) hw hR
    hnatSup hnatL1 hrowNat
  obtain ⟨hfull, hsf⟩ := B.actualQuadratics_eq_covariances xi q
  rw [hfull, hsf] at hquad
  simpa only [mul_assoc] using hquad



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

/- Source module: Erdos390.Full.PaperCanonicalLemma86RelativePrimePowerEventually -/
section


/-!
# Canonical relative prime-power clause of paper Lemma 8.6

The paper needs the replacement of full prime valuations by squarefree prime
indicators at the relative `w^2` scale.  This file performs that replacement
for the literal regression produced by the exact finite nuisance-Schur map.

The nonvanishing constant is selected before `W`, the permitted mesh, and the
effective tilt box.  All later dependence is confined to a named remainder
whose product with `log (log n)` tends to zero (and which therefore itself
tends to zero).  No `PrimePowerTransferBounds`, weighted-row estimate,
coefficient bound, convergence assertion, or abstract inverse is exposed at
the public call site.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport PrimeSums
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

/-- An eventually nonnegative error whose product with `log (log n)` tends
to zero tends to zero. -/
private theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero_relative
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

set_option maxHeartbeats 2500000 in
/--
Assumption-free, paper-order, relative prime-power estimate for the same
`q^reg` which is obtained from the exact finite nuisance-Schur equivalence.

The output includes the same-map identity and both inverse bounds so a later
umbrella theorem can reuse this exact `e`; it never needs to identify two
separately chosen equivalences after the fact.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∃ Creg : ℝ, 0 ≤ Creg ∧
        Creg = Csharp * (2 * Crow) ∧
      ∃ Crel : ℝ, 0 < Crel ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∃ epsilonRel : ℕ → ℝ,
          (∀ᶠ n : ℕ in atTop, 0 ≤ epsilonRel n) ∧
          Tendsto epsilonRel atTop (nhds 0) ∧
          Tendsto
            (fun n : ℕ ↦ epsilonRel n * Real.log (Scale.L n))
              atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
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
                (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                    (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                  B.partition =
                    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                      M hdelta B.n_gt_one hWne S) →
                (hscale : B.w = delta + eta) →
                ∀ (T : BarycentricTarget B.sampleData)
                  (hTmargin : marginFloor ≤ T.cellMassMargin)
                  (hbaseline : B.baseline = T.baseline),
                  (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.partition.deviation p| ≤ B.w) ∧
                  B.partition.totalL1 ≤ 7 * B.w ∧
                  B.w ^ 2 ≤
                    (456 / cMesh ^ 2) * B.partition.variance ∧
                  B.partition.variance ≤ 4 * B.w ^ 2 ∧
                  B.partition.variance ≤ B.partition.centerEnergy ∧
                  ∃ e : ∀ (z : B.EffectiveParamSpace),
                      z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ) →
                        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                      e z hz q =
                        B.actualBandSchurLinearMap
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) q) ∧
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                      paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one)
                          ((e z hz).symm v) ≤
                        Csharp *
                          paperSharpNorm B.harmonicMass B.bandCenter
                            (B.partition.center_ne_zero B.n_gt_one) v) ∧
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                      ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖) ∧
                    ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)),
                      (∀ j,
                        |B.normalizedBandCovarianceRow
                            (B.effectiveParamEquiv z)
                            (B.nuisanceResidualScore
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              B.slowScore) j| ≤
                          (Crow * B.w) * B.bandCenter j) ∧
                      B.actualBandSchurLinearMap
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) =
                        B.actualBandRegressionTarget
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) ∧
                      paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one)
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤ Creg * B.w ∧
                      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                        |B.actualCompensatedCoefficient
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) p| ≤ (1 + Creg) * B.w) ∧
                      B.partition.compensatedL1
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤
                        (7 + Creg * (2 * Real.log 4)) * B.w ∧
                      B.partition.compensatedL2Sq
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤
                        2 * (4 + Creg ^ 2 * (2 * Real.log 4)) * B.w ^ 2 ∧
                      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (B.postBandPrimeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))
                          (B.postBandPrimeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz))) -
                        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (B.postBandSquarefreeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))
                          (B.postBandSquarefreeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))| ≤
                        (Crel * (1 / (B.sampleData.W : ℝ)) +
                          epsilonRel B.sampleData.n) * B.w ^ 2 := by
  obtain ⟨baseTol, hbaseTol, Csharp, hCsharp, Cordinary, hCordinary,
      Crow, hCrow, Wbase, hBase⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients
      cMesh hcMesh
  let Creg : ℝ := Csharp * (2 * Crow)
  let K : ℝ := 2 * Real.log 4
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  let relativeFactor : ℝ := (1 + Creg) * (7 + Creg * K)
  let Crel : ℝ := relativeFactor * Cpow
  let W₀ : ℕ := max Wbase 2
  have hCreg : 0 ≤ Creg := by
    dsimp only [Creg]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hCpow : 0 < Cpow := by
    simpa only [Cpow] using
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant_pos
  have hrelativeFactor : 0 < relativeFactor := by
    dsimp only [relativeFactor]
    positivity
  have hCrel : 0 < Crel := by
    dsimp only [Crel]
    positivity
  refine ⟨baseTol, hbaseTol, Csharp, hCsharp, Cordinary, hCordinary,
    Crow, hCrow, Creg, hCreg, rfl, Crel, hCrel, W₀, ?_⟩
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instFintype _instDecidable _instNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWbase : Wbase ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWone : 1 < W := by
    dsimp only [W₀] at hW
    omega
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  let Acoef : ℝ := 3 * (a : ℝ)
  let Aphys : ℝ := 3 * (a : ℝ)
  have hAcoef : 0 ≤ Acoef := by dsimp only [Acoef]; positivity
  have hAphys : 0 ≤ Aphys := by dsimp only [Aphys]; positivity
  obtain ⟨_hCpowTerminal, hPowerFamily⟩ :=
    boxIndependent_canonicalRaw_actualWeightedRow
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  obtain ⟨epsilon75, hepsilon750, _hepsilon75T, hepsilon75Rate,
      hcombinedRateRaw, Npower, hpower⟩ :=
    hPowerFamily W hWone hHeadLe Acoef hAcoef Aphys hAphys
  let combined : ℕ → ℝ := fun n ↦
    canonicalCombinedPowerCorrection
      Phead I U Cprom Cbank W Acoef Aphys n
  let epsilonRel : ℕ → ℝ := fun n ↦
    relativeFactor * (epsilon75 n + combined n)
  have hcombinedRate : Tendsto
      (fun n : ℕ ↦ combined n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    simpa only [combined, canonicalCombinedPowerCorrection] using
      hcombinedRateRaw
  have hcombinedNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ combined n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact canonicalCombinedPowerCorrection_nonneg
      Phead I hU hAphys hWone hn
  have hepsilonRelNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ epsilonRel n := by
    filter_upwards [hcombinedNonneg] with n hcombinedN
    dsimp only [epsilonRel]
    exact mul_nonneg hrelativeFactor.le
      (add_nonneg (hepsilon750 n) hcombinedN)
  have hepsilonRelRate : Tendsto
      (fun n : ℕ ↦ epsilonRel n * Real.log (Scale.L n))
        atTop (nhds 0) := by
    have hsum := hepsilon75Rate.add hcombinedRate
    have hconst : Tendsto (fun _n : ℕ ↦ relativeFactor)
        atTop (nhds relativeFactor) := tendsto_const_nhds
    have hscaled := hconst.mul hsum
    simpa only [epsilonRel, add_mul, mul_add, mul_assoc,
      zero_mul, mul_zero, add_zero] using hscaled
  have hepsilonRel : Tendsto epsilonRel atTop (nhds 0) :=
    tendsto_zero_of_eventually_nonneg_mul_logL_zero_relative
      epsilonRel hepsilonRelNonneg hepsilonRelRate
  have hBaseN := hBase W hWbase M hdelta hPermitted hfine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hBandT := eventually_bandTReciprocalSum_le W
  refine ⟨epsilonRel, hepsilonRelNonneg, hepsilonRel,
    hepsilonRelRate, ?_⟩
  filter_upwards [hBaseN, hBandT, hcombinedNonneg,
    eventually_ge_atTop Npower] with
      n hBaseAt hBandTAt hcombinedNonnegAt hnPower
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    hscale T hTmargin hbaseline
  subst n
  subst W
  obtain ⟨hdev, hdevL1, hvarLower, hdevL2, hcenter,
      e, he, hinv, hinvOrd, hBaseZ⟩ :=
    hBaseAt B rfl rfl hBWlarge hsep hremaining hcanonical hpartition
      hscale T hTmargin hbaseline
  have hdevW : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    simpa only [hscale] using hdev
  have hdevL1W : B.partition.totalL1 ≤ 7 * B.w := by
    simpa only [hscale] using hdevL1
  have hvarLowerW : B.w ^ 2 ≤
      (456 / cMesh ^ 2) * B.partition.variance := by
    simpa only [hscale] using hvarLower
  have hdevL2W : B.partition.variance ≤ 4 * B.w ^ 2 := by
    simpa only [hscale] using hdevL2
  refine ⟨hdevW, hdevL1W, hvarLowerW, hdevL2W, hcenter,
    e, he, hinv, hinvOrd, ?_⟩
  intro z hz
  obtain ⟨hslow, hnormal, hqSharp, hcoeffSup,
      hcoeffL1, hcoeffL2⟩ := hBaseZ z hz
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
        PiLp.norm_apply_le (B.nuisanceParameter xi)
          NuisanceCoord.physical
      _ ≤ Aphys := by simpa only [Acoef, Aphys] using hnuisance
  let R : ℝ := Cpow * (1 / (B.sampleData.W : ℝ)) +
    epsilon75 B.sampleData.n + combined B.sampleData.n
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCpow.le (by positivity))
        (hepsilon750 B.sampleData.n)) hcombinedNonnegAt
  have hrowRaw := hpower B xi hnPower rfl hsep hremaining hcanonical
    heta hphys
  have hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R := by
    intro p
    simpa only [R, combined, canonicalCombinedPowerCorrection] using
      hrowRaw p
  let hgamma : 0 < B.canonicalEffectiveNuisanceGamma
      I U (3 * (a : ℝ)) T :=
    B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  let hgap : ∀ v,
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator xi v) :=
    B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU
      (by intro sigma; rw [hcanonical]; rfl)
      (by intro sigma; rw [hcanonical]; rfl)
      T hbaseline hBWlarge z hz
  let q := B.actualBandRegression xi hgamma hgap (e z hz)
  have hq : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ Creg * B.w := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hqSharp
  have hrelative := B.actual_primePower_relative_variance_bound_of_row
    xi q hCreg hK B.w_pos.le hR hq hBandTAt hdevW hdevL1W hdevL2W hrow
  have hcoeffSupW : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient q p| ≤ (1 + Creg) * B.w := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hcoeffSup
  have hcoeffL1W : B.partition.compensatedL1 q ≤
      (7 + Creg * (2 * Real.log 4)) * B.w := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hcoeffL1
  have hcoeffL2W : B.partition.compensatedL2Sq q ≤
      2 * (4 + Creg ^ 2 * (2 * Real.log 4)) * B.w ^ 2 := by
    simpa only [q, xi, hgamma, hgap, Creg, hscale] using hcoeffL2
  refine ⟨by simpa only [xi, hgamma, hgap] using hslow,
    by simpa only [q, xi, hgamma, hgap] using hnormal,
    hq, hcoeffSupW, hcoeffL1W, hcoeffL2W, ?_⟩
  have hrelativeRhs : relativeFactor * R * B.w ^ 2 =
      (Crel * (1 / (B.sampleData.W : ℝ)) +
        epsilonRel B.sampleData.n) * B.w ^ 2 := by
    dsimp only [R, Crel, epsilonRel]
    ring
  rw [hrelativeRhs] at hrelative
  simpa only [q, xi, hgamma, hgap] using hrelative

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal003_001.{u_1} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
