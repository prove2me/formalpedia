-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:12.897029+00:00
-- url     : https://prove2.me/submissions/d2ec627b-e435-4037-9460-aad5abda9db5

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
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_diagonal_sub_reference_le
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles

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









theorem coord_decomposition (p : Prime) :
    d.coord p = d.lift d.center p - d.cellDeviation p := by
  simp [lift, cellDeviation]



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



theorem physical_completion (q : Band → ℝ) (lambda mu : ℝ)
    (hq : d.inGauge q) (hden : d.centerEnergy + d.cellVariance ≠ 0) :
    d.physicalSq (fun j => q j + lambda * d.center j) mu =
      d.bandNormSq q +
        lambda ^ 2 * (d.centerEnergy * d.cellVariance) /
          (d.centerEnergy + d.cellVariance) +
        (d.centerEnergy + d.cellVariance) *
          (mu - lambda * d.centerEnergy /
            (d.centerEnergy + d.cellVariance)) ^ 2 := by
  rw [d.physicalSq_expansion q lambda mu hq]
  field_simp
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

/- Source module: Erdos390.Full.ArithmeticBandGeometry -/
section


/-!
# Exact arithmetic band geometry

This instantiates the finite weighted-band algebra with the paper's actual
prime set, harmonic weights `1/p`, and logarithmic coordinates `t_p`.  In
particular the centering identity is arithmetic, not a continuum identity;
this is the correction required by the audit of Section 8.4.
-/

namespace Erdos390.Full

noncomputable section

open ArithmeticModel

namespace ArithmeticBandGeometry





namespace Partition

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]





















/-- Exact completion of squares, hence the arithmetic distance is at least
the gauge norm. -/
theorem physicalSq_completion (P : Partition n W Band)
    (q : Band → ℝ) (lambda mu : ℝ) (hq : P.data.inGauge q)
    (hden : P.centerEnergy + P.variance ≠ 0) :
    P.data.physicalSq (fun j ↦ q j + lambda * P.center j) mu =
      P.data.bandNormSq q +
        lambda ^ 2 * (P.centerEnergy * P.variance) /
          (P.centerEnergy + P.variance) +
        (P.centerEnergy + P.variance) *
          (mu - P.minimizingMu lambda) ^ 2 := by
  exact P.data.physical_completion q lambda mu hq hden



/-- The exact arithmetic completion of squares gives a lower bound at every
physical coefficient, not only at the minimizing coefficient.  This is the
finite-`n` quotient gap used for the compensated slow direction; in
particular, it does not compare an arithmetic centre with a continuum
centre. -/
theorem physicalSq_ge_gauge_add_harmonic_gap
    (P : Partition n W Band)
    (q : Band → ℝ) (lambda mu : ℝ) (hq : P.data.inGauge q)
    (hden : 0 < P.centerEnergy + P.variance) :
    P.data.bandNormSq q +
        lambda ^ 2 * (P.centerEnergy * P.variance) /
          (P.centerEnergy + P.variance) ≤
      P.data.physicalSq (fun j ↦ q j + lambda * P.center j) mu := by
  rw [P.physicalSq_completion q lambda mu hq hden.ne']
  exact le_add_of_nonneg_right (mul_nonneg hden.le (sq_nonneg _))

/-- If the within-cell variance is no larger than the centre energy, the
physical quotient distance for the coefficient `q + center` is at least
half of the literal arithmetic variance.  All quantities in the statement
are the finite prime-band quantities. -/
theorem half_variance_le_physicalSq
    (P : Partition n W Band)
    (q : Band → ℝ) (mu : ℝ) (hq : P.data.inGauge q)
    (hcenter : 0 < P.centerEnergy)
    (hvariance : P.variance ≤ P.centerEnergy) :
    P.variance / 2 ≤
      P.data.physicalSq (fun j ↦ q j + P.center j) mu := by
  have hvar : 0 ≤ P.variance :=
    P.data.primeNormSq_nonneg P.data.cellDeviation
  have hden : 0 < P.centerEnergy + P.variance :=
    add_pos_of_pos_of_nonneg hcenter hvar
  have hfrac :
      P.variance / 2 ≤
        P.centerEnergy * P.variance /
          (P.centerEnergy + P.variance) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hgap := P.physicalSq_ge_gauge_add_harmonic_gap
    q 1 mu hq hden
  have hband : 0 ≤ P.data.bandNormSq q :=
    P.data.bandNormSq_nonneg q
  norm_num only [one_pow, one_mul] at hgap
  linarith



end Partition

end ArithmeticBandGeometry

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





/-! ## The removable axis singularity and a continuous kernel representative -/

















































/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

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







/-- Membership in the paper's raw arithmetic gauge is definitionally the
finite weighted-band gauge used by the exact quotient identity. -/
theorem rawGauge_inGauge
    (q : RawGaugeSpace P.mass P.center) : P.data.inGauge q.1 := by
  change (∑ j, P.mass j * P.center j * q.1 j) = 0
  have hq := q.property
  change (∑ j, rawGaugeWeight P.mass P.center j * q.1 j) = 0 at hq
  exact hq

/-- Direct raw-gauge form of the exact finite physical quotient gap. -/
theorem half_variance_le_physicalSq_rawGauge [Nonempty Band]
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center) (mu : ℝ)
    (hvariance : P.variance ≤ P.centerEnergy) :
    P.variance / 2 ≤
      P.data.physicalSq (fun j ↦ q.1 j + P.center j) mu := by
  exact P.half_variance_le_physicalSq q.1 mu
    (P.rawGauge_inGauge q) (P.centerEnergy_pos hn) hvariance

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









theorem weightedL1_compensated_eq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center) :
    weightedL1 (reciprocalWeight (n := n) (W := W))
        (compensatedPrimeCoefficient P q) =
      P.compensatedL1 q := by
  rfl

theorem weightedL2Sq_compensated_eq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center) :
    weightedL2Sq (reciprocalWeight (n := n) (W := W))
        (compensatedPrimeCoefficient P q) =
      P.compensatedL2Sq q := by
  rfl

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

/-- The graph distance of the compensated coefficient is the exact finite
arithmetic physical distance, with the harmless shift `mu ↦ mu+1`. -/
theorem primePhysicalDistance_compensated_eq_physicalSq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    (mu : ℝ) :
    primePhysicalDistance n (compensatedPrimeCoefficient P q) mu =
      P.data.physicalSq (fun j ↦ -q.1 j + P.center j) (mu + 1) := by
  unfold primePhysicalDistance compensatedPrimeCoefficient
    Erdos390.Lemma84.WeightedBandData.physicalSq
    Erdos390.Lemma84.WeightedBandData.primeNormSq
    Erdos390.Lemma84.WeightedBandData.primeInner
    Erdos390.Lemma84.WeightedBandData.residual
    Erdos390.Lemma84.WeightedBandData.lift
    compensatedCoefficient regressionCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1 - q.1 (P.band p) -
        mu * tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) *
      ((-q.1 (P.band p) + P.center (P.band p)) -
        (mu + 1) * tPrime n p.1) *
      ((-q.1 (P.band p) + P.center (P.band p)) -
        (mu + 1) * tPrime n p.1)
  ring

/-- The exact arithmetic completion of squares applies at the anchor mean,
or indeed at any scalar representative of the scale-null direction. -/
theorem half_variance_le_primePhysicalDistance_compensated
    [Nonempty Band] (hn : 1 < n)
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    (mu : ℝ) (hvariance : P.variance ≤ P.centerEnergy) :
    P.variance / 2 ≤
      primePhysicalDistance n (compensatedPrimeCoefficient P q) mu := by
  rw [primePhysicalDistance_compensated_eq_physicalSq P q mu]
  simpa only [neg_neg] using
    P.half_variance_le_physicalSq_rawGauge hn (-q) (mu + 1) hvariance

/-- A row residual of size `rowError * t_p` contributes at most
`rowError * sum_p c_p²/p`.  This is the relative estimate needed in the
moving low cell: an additive `o(1)` row bound would not suffice. -/
theorem abs_primeRowResidualContribution_le
    (hn : 1 < n)
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    {rowError : ℝ}
    (hrow : ∀ p : Prime n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        rowError * tPrime n p.1) :
    |∑ p, primeWeight n p *
        rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
          (dirichletCoordinate n (compensatedPrimeCoefficient P q) p) ^ 2| ≤
      rowError * P.compensatedL2Sq q := by
  simpa only [primeCoefficientL2Sq, compensatedPrimeCoefficient,
    compensatedL2Sq] using
      (PrimeSquarefreeDirichletGeometry.abs_rowResidualContribution_le
        hn (compensatedPrimeCoefficient P q) hrow)



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

/-- The subtype-indexed squarefree quadratic is exactly the covariance of
the paper's literal post-band squarefree score. -/
theorem subtypeSquarefreeQuadratic_actual_eq_covariance
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    subtypeSquarefreeQuadratic (B.actualValuationLaw xi)
        (compensatedPrimeCoefficient B.partition q) =
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let cNat : ℕ → ℝ := B.actualCompensatedNatCoefficient q
  have hquad := (B.actualQuadratics_eq_covariances xi q).2
  change PaperPrimePowerRelativeQuadratic.squarefreeQuadratic
      (B.actualValuationLaw xi)
      (primeBand B.sampleData.n B.sampleData.W) cNat = _ at hquad
  rw [← hquad]
  unfold subtypeSquarefreeQuadratic matrixQuadratic
    PaperPrimePowerRelativeQuadratic.squarefreeQuadratic
  have houter := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
      cNat p * cNat r * (B.actualValuationLaw xi).covII p r)
  rw [← houter]
  apply Finset.sum_congr rfl
  intro p hp
  have hinner := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun r ↦ cNat p.1 * cNat r *
      (B.actualValuationLaw xi).covII p.1 r)
  rw [← hinner]
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [cNat]
  unfold compensatedPrimeCoefficient
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]
  rw [B.actualCompensatedNatCoefficient_of_mem q r.2]
  rw [B.partition_compensatedCoefficient_eq q p]
  rw [B.partition_compensatedCoefficient_eq q r]







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

/-- The fixed Dickman gap gives the exact compensated prime-reference lower
without an `n`-dependent existential witness. -/
theorem canonicalSlowKappa_primeReference_compensated_lower
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Band]
    (B : BridgeData Head Band)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy) :
    ∀ q : B.RawBandGauge,
      (canonicalSlowKappa / 4) *
            anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance -
          rowError * B.partition.compensatedL2Sq q ≤
        primeReferenceQuadratic B.sampleData.n
          (compensatedPrimeCoefficient B.partition q) := by
  intro q
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  let mu : ℝ := anchorMean B.sampleData.n anchor c
  have hdistance : B.partition.variance / 2 ≤
      primePhysicalDistance B.sampleData.n c mu :=
    half_variance_le_primePhysicalDistance_compensated B.partition
      B.n_gt_one q mu hvariance
  have hcoef : 0 ≤ (canonicalSlowKappa / 2) *
      anchorMass (primeWeight B.sampleData.n) anchor :=
    mul_nonneg (div_nonneg canonicalSlowKappa_pos.le (by norm_num)) hmass.le
  have hscaled := mul_le_mul_of_nonneg_left hdistance hcoef
  have henergyLower :
      (canonicalSlowKappa / 4) *
            anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance ≤
        dirichletEnergy (primeWeight B.sampleData.n)
          (primeKernel B.sampleData.n) (dirichletCoordinate B.sampleData.n c) := by
    calc
      (canonicalSlowKappa / 4) *
            anchorMass (primeWeight B.sampleData.n) anchor *
            B.partition.variance =
          ((canonicalSlowKappa / 2) *
            anchorMass (primeWeight B.sampleData.n) anchor) *
              (B.partition.variance / 2) := by ring
      _ ≤ ((canonicalSlowKappa / 2) *
            anchorMass (primeWeight B.sampleData.n) anchor) *
              primePhysicalDistance B.sampleData.n c mu := hscaled
      _ ≤ dirichletEnergy (primeWeight B.sampleData.n)
            (primeKernel B.sampleData.n)
            (dirichletCoordinate B.sampleData.n c) :=
        canonicalSlowKappa_primeDirichlet_anchor_lower B.n_gt_one
          anchor hinterior hmass c
  have hresAbs := abs_primeRowResidualContribution_le
    B.partition B.n_gt_one q hrow
  have hresLower :
      -(rowError * B.partition.compensatedL2Sq q) ≤
        ∑ p, primeWeight B.sampleData.n p *
          rowResidual (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p *
            (dirichletCoordinate B.sampleData.n c p) ^ 2 :=
    neg_le_of_abs_le (by simpa only [c] using hresAbs)
  rw [primeReferenceQuadratic_eq_dirichlet_add_residual B.n_gt_one c]
  linarith

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

/-- Exact actual squarefree lower with the globally fixed
`canonicalSlowKappa`. -/
theorem actualSquarefree_compensated_lower_canonicalKappa_of_profiles
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    {rowError : ℝ}
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |covarianceKernel (tPrime B.sampleData.n p)
          (tPrime B.sampleData.n p)| ≤ CKernel) :
    (canonicalSlowKappa / 4) *
          anchorMass (primeWeight B.sampleData.n) anchor *
          B.partition.variance -
        rowError * B.partition.compensatedL2Sq q -
        ((4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
          (2 * Eprofile) * B.partition.compensatedL2Sq q +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) *
            weightedL2SqSecond reciprocalWeight
              (compensatedPrimeCoefficient B.partition q)) ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle hKernel
  have herror := abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    (B.actualValuationLaw xi) c hentry
  have herror' :
      |subtypeSquarefreeQuadratic (B.actualValuationLaw xi) c -
          primeReferenceQuadratic B.sampleData.n c| ≤
        (4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
          (2 * Eprofile) * B.partition.compensatedL2Sq q +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * weightedL2SqSecond reciprocalWeight c := by
    simpa only [c, weightedL1_compensated_eq,
      weightedL2Sq_compensated_eq] using herror
  have hlower := neg_le_of_abs_le herror'
  rw [B.subtypeSquarefreeQuadratic_actual_eq_covariance xi q] at hlower
  have href := canonicalSlowKappa_primeReference_compensated_lower
    B anchor hinterior hmass hrow hvariance q
  linarith



end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

/- Source module: Erdos390.Full.PaperActualLemma86PaperScale -/
section


/-!
# Paper-scale finite slow-variance lower

The older relative lemma normalized the partition variance by the special
factor `1/16`.  A permitted two-parameter paper mesh instead supplies a
uniform factor depending only on the previously fixed regularity constant.
This file keeps that factor literal.  No comparison between `delta` and
`eta` is encoded in the finite statement.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open OmittedTiltPairChamber PrimePowerCovariance
open PaperPrimePowerChamberError PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperWeightedInverseExport PaperCanonicalSlowKappa
open FiniteSignedQuadraticEntryTransfer SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









/-- Exact relative squarefree lower for an arbitrary nonnegative variance
factor.  The proof retains the literal arithmetic anchor and does not
replace the two mesh parameters by one another. -/
theorem actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w varianceFactor rowError Eprofile CKernel anchorFloor : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hvarianceFactor : 0 ≤ varianceFactor)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCKernel : 0 ≤ CKernel) (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hvarLower : varianceFactor * w ^ 2 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel) :
    paperScaleSquarefreeSlowConstant varianceFactor anchorFloor rowError
        Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let CL1 := slowL1Constant C K
  let CL2 := slowL2Constant C K
  let eOff := 4 * pairCovarianceScale Eprofile
  let eDiag := 2 * Eprofile
  let eSecond := signedSecondConstant Eprofile CKernel
  let invW := 1 / (B.sampleData.W : ℝ)
  have hthree := B.partition.compensatedCoefficient_three_bounds
    B.n_gt_one q hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hL1 : B.partition.compensatedL1 q ≤ CL1 * w := by
    simpa only [CL1, slowL1Constant] using hthree.2.1
  have hL2 : B.partition.compensatedL2Sq q ≤ CL2 * w ^ 2 := by
    simpa only [CL2, slowL2Constant] using hthree.2.2
  have hCL1 : 0 ≤ CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hCL2 : 0 ≤ CL2 := by
    dsimp only [CL2, slowL2Constant]
    positivity
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hL1Sq : B.partition.compensatedL1 q ^ 2 ≤
      CL1 ^ 2 * w ^ 2 := by
    have hsquare := (sq_le_sq₀ hL1nonneg (mul_nonneg hCL1 hw)).2 hL1
    nlinarith
  have hSecondRaw :=
    weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
      (n := B.sampleData.n) hW
      (compensatedPrimeCoefficient B.partition q)
  have hInvW : 0 ≤ invW := by dsimp only [invW]; positivity
  have hSecond :
      weightedL2SqSecond reciprocalWeight
          (compensatedPrimeCoefficient B.partition q) ≤
        invW * CL2 * w ^ 2 := by
    rw [weightedL2Sq_compensated_eq] at hSecondRaw
    calc
      weightedL2SqSecond reciprocalWeight
          (compensatedPrimeCoefficient B.partition q) ≤
          invW * B.partition.compensatedL2Sq q := by
        simpa only [invW] using hSecondRaw
      _ ≤ invW * (CL2 * w ^ 2) :=
        mul_le_mul_of_nonneg_left hL2 hInvW
      _ = invW * CL2 * w ^ 2 := by ring
  have hlowerExact :=
    B.actualSquarefree_compensated_lower_canonicalKappa_of_profiles
      xi q anchor hinterior hmass hrow hvariance hEprofile
      hpair hsingle (fun p hp ↦ hKernel ⟨p, hp⟩ ⟨p, hp⟩)
  have hk4 : 0 ≤ canonicalSlowKappa / 4 :=
    div_nonneg canonicalSlowKappa_pos.le (by norm_num)
  have hmassvar :
      anchorFloor * (varianceFactor * w ^ 2) ≤
        anchorMass (primeWeight B.sampleData.n) anchor *
          B.partition.variance :=
    mul_le_mul hAnchorMass hvarLower
      (mul_nonneg hvarianceFactor (sq_nonneg _)) hmass.le
  have hmain := mul_le_mul_of_nonneg_left hmassvar hk4
  have hrowLoss := mul_le_mul_of_nonneg_left hL2 hrowError
  have heOff : 0 ≤ eOff := by
    dsimp only [eOff]
    exact mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile)
  have heDiag : 0 ≤ eDiag := by dsimp only [eDiag]; positivity
  have heSecond : 0 ≤ eSecond := by
    dsimp only [eSecond, signedSecondConstant]
    positivity
  have hoffLoss := mul_le_mul_of_nonneg_left hL1Sq heOff
  have hdiagLoss := mul_le_mul_of_nonneg_left hL2 heDiag
  have hsecondLoss := mul_le_mul_of_nonneg_left hSecond heSecond
  have htarget :
      paperScaleSquarefreeSlowConstant varianceFactor anchorFloor rowError
          Eprofile CKernel C K invW * w ^ 2 ≤
        (canonicalSlowKappa / 4) *
              anchorMass (primeWeight B.sampleData.n) anchor *
              B.partition.variance -
          rowError * B.partition.compensatedL2Sq q -
          (eOff * B.partition.compensatedL1 q ^ 2 +
            eDiag * B.partition.compensatedL2Sq q +
            eSecond * weightedL2SqSecond reciprocalWeight
              (compensatedPrimeCoefficient B.partition q)) := by
    dsimp only [paperScaleSquarefreeSlowConstant, CL1, CL2,
      eOff, eDiag, eSecond]
    nlinarith [hmain, hrowLoss, hoffLoss, hdiagLoss, hsecondLoss]
  simpa only [invW] using htarget.trans hlowerExact





end BridgeData

end Erdos390.Full.PaperBridgeFit

end

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [Nonempty.{u_2 + 1} Band] (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {C K w varianceFactor rowError Eprofile CKernel anchorFloor : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) K →
      LE.le.{0} (0 : Real) w →
        LE.le.{0} (0 : Real) varianceFactor →
          LE.le.{0} (0 : Real) rowError →
            LE.le.{0} (0 : Real) Eprofile →
              LE.le.{0} (0 : Real) CKernel →
                LT.lt.{0} (0 : Nat)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                  LE.le.{0}
                      (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                        (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                          (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                        q)
                      (HMul.hMul.{0, 0, 0} C w) →
                    LE.le.{0}
                        (Erdos390.Full.PrimeSums.bandTReciprocalSum
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        K →
                      (∀
                          (p :
                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                          LE.le.{0}
                            (abs.{0}
                              (Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{u_2}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p))
                            w) →
                        LE.le.{0}
                            (Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{u_2}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                            (HMul.hMul.{0, 0, 0} (7 : Real) w) →
                          LE.le.{0} (HMul.hMul.{0, 0, 0} varianceFactor (HPow.hPow.{0, 0, 0} w (2 : Nat)))
                              (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                            LE.le.{0}
                                (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} w (2 : Nat))) →
                              LE.le.{0}
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                                ∀
                                  (anchor :
                                    Finset.{0}
                                      (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))),
                                  (∀
                                      (p :
                                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                      Membership.mem.{0, 0} anchor p →
                                        Membership.mem.{0, 0}
                                          (Set.Icc.{0} (1 / 8 : Real) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real)))
                                          (Erdos390.Full.ArithmeticModel.tPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            ↑p)) →
                                    LT.lt.{0} (0 : Real)
                                        (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                          (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                          anchor) →
                                      LE.le.{0} anchorFloor
                                          (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                            (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            anchor) →
                                        (∀
                                            (p :
                                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                            LE.le.{0}
                                              (abs.{0}
                                                (Erdos390.Full.FiniteAnchoredDirichletQuadratic.rowResidual.{0}
                                                  (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)))
                                                  (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)))
                                                  (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)))
                                                  p))
                                              (HMul.hMul.{0, 0, 0} rowError
                                                (Erdos390.Full.ArithmeticModel.tPrime
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                  ↑p))) →
                                          (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                              Membership.mem.{0, 0}
                                                  (Erdos390.Full.ArithmeticModel.primeBand
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)))
                                                  p →
                                                ∀ (r : Nat),
                                                  Membership.mem.{0, 0}
                                                      (Finset.erase.{0}
                                                        (Erdos390.Full.ArithmeticModel.primeBand
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B)))
                                                        p)
                                                      r →
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.FiniteProbability.expect.{0}
                                                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                  u_2}
                                                                B xi c))
                                                            fun omega =>
                                                            Erdos390.Full.ArithmeticModel.divInd
                                                              (Erdos390.Full.OmittedTiltPairChamber.pairPower p r
                                                                (1 : Nat) (1 : Nat))
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                    u_2}
                                                                  B xi c)
                                                                omega))
                                                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B))
                                                            (Erdos390.Full.OmittedTiltPairChamber.pairPower p r
                                                              (1 : Nat) (1 : Nat)))))
                                                      (HMul.hMul.{0, 0, 0} Eprofile
                                                        (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p r
                                                          (1 : Nat) (1 : Nat)))) →
                                            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                Membership.mem.{0, 0}
                                                    (Erdos390.Full.ArithmeticModel.primeBand
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B)))
                                                    p →
                                                  LE.le.{0}
                                                    (abs.{0}
                                                      (HSub.hSub.{0, 0, 0}
                                                        (Erdos390.Full.FiniteProbability.expect.{0}
                                                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                u_2}
                                                              B xi c))
                                                          fun omega =>
                                                          Erdos390.Full.ArithmeticModel.divInd p
                                                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                  u_2}
                                                                B xi c)
                                                              omega))
                                                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          p)))
                                                    (HMul.hMul.{0, 0, 0} Eprofile
                                                      (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p
                                                        (1 : Nat)))) →
                                              (∀
                                                  (p r :
                                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))),
                                                  LE.le.{0}
                                                    (abs.{0}
                                                      (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                                                        (Erdos390.Full.ArithmeticModel.tPrime
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          ↑p)
                                                        (Erdos390.Full.ArithmeticModel.tPrime
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          ↑r)))
                                                    CKernel) →
                                                LE.le.{0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.paperScaleSquarefreeSlowConstant
                                                      varianceFactor anchorFloor rowError Eprofile CKernel C K
                                                      (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                        ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))))
                                                    (HPow.hPow.{0, 0, 0} w (2 : Nat)))
                                                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1,
                                                        u_2}
                                                      B q)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1,
                                                        u_2}
                                                      B q)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
