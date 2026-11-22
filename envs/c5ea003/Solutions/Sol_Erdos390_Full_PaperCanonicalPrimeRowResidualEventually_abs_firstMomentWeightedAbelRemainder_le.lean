-- Prove2me | solution 1 for Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_firstMomentWeightedAbelRemainder_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:21:46.905565+00:00
-- url     : https://prove2.me/submissions/0f77de67-782e-4dd6-a935-215d0f47516c

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005

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



lemma abs_firstMomentAbelCoefficient_le
    {M s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u) :
    |firstMomentAbelCoefficient s z x| ≤
      (M * s) / (x * Real.log x) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hdenpos : 0 < x * Real.log x := mul_pos hxpos hlogxpos
  unfold firstMomentAbelCoefficient weightedAbelCoefficient
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hPhi s hs _ ht) hdenpos.le

lemma abs_firstMomentAbelDerivative_le
    {M s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u) :
    |firstMomentAbelDerivative s z x| ≤
      (M * s) / (x ^ 2 * Real.log x * Real.log z) +
        (M * s) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
  have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
  have hplus : 0 ≤ Real.log x + 1 := by linarith
  unfold firstMomentAbelDerivative weightedAbelCoefficientDerivative
  calc
    |firstMomentKernelDerivative s (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z) -
        firstMomentKernel s (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| ≤
      |firstMomentKernelDerivative s (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z)| +
        |firstMomentKernel s (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| := abs_sub _ _
    _ = |firstMomentKernelDerivative s (realLogCoordinate z x)| /
          (x ^ 2 * Real.log x * Real.log z) +
        |firstMomentKernel s (realLogCoordinate z x)| * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      rw [abs_div, abs_div]
      simp only [abs_mul]
      rw [abs_of_nonneg (sq_nonneg x), abs_of_pos hlogxpos,
        abs_of_pos hlogzpos, abs_of_nonneg hplus,
        abs_of_nonneg (sq_nonneg (Real.log x))]
    _ ≤ (M * s) / (x ^ 2 * Real.log x * Real.log z) +
        (M * s) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      exact add_le_add
        (div_le_div_of_nonneg_right (hPhiPrime s hs _ ht) hden₁.le)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hPhi s hs _ ht) hplus) hden₂.le)

lemma abs_firstMomentAbelCoefficient_mul_thetaError_le
    {C M s z x : ℝ} (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |firstMomentAbelCoefficient s z x * thetaError x| ≤
      C * (M * s) / Real.log x ^ 4 := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hcoeff := abs_firstMomentAbelCoefficient_le hs hz hx1 hxz hPhi
  rw [abs_mul]
  calc
    |firstMomentAbelCoefficient s z x| * |thetaError x| ≤
        ((M * s) / (x * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      apply mul_le_mul hcoeff hTheta (abs_nonneg _)
      exact div_nonneg (mul_nonneg hM hs.1) (by positivity)
    _ = C * (M * s) / Real.log x ^ 4 := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

lemma abs_firstMomentAbelDerivative_mul_thetaError_le
    {C M s z x : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |firstMomentAbelDerivative s z x * thetaError x| ≤
      mertensErrorMajorant (2 * C * (M * s)) x := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log hxpos hxz
  have hplus : Real.log x + 1 ≤ 3 * Real.log x := by linarith
  have hderiv := abs_firstMomentAbelDerivative_le hs hz hx1 hxz
    hPhi hPhiPrime
  have hsimplified :
      (M * s) / (x ^ 2 * Real.log x * Real.log z) +
          (M * s) * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2) ≤
        5 * (M * s) / (x ^ 2 * Real.log x) := by
    have hMs : 0 ≤ M * s := mul_nonneg hM hs.1
    have hdenx : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
    have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
    have hden₃ : 0 < x ^ 2 * Real.log x := by positivity
    have hfirst :
        (M * s) / (x ^ 2 * Real.log x * Real.log z) ≤
          (M * s) / (x ^ 2 * Real.log x ^ 2) := by
      apply (div_le_div_iff₀ hden₁ hden₂).2
      apply mul_le_mul_of_nonneg_left _ hMs
      nlinarith [mul_pos hdenx hlogpos]
    have hsecond :
        (M * s) * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
          3 * (M * s) / (x ^ 2 * Real.log x) := by
      calc
        _ ≤ (M * s) * (3 * Real.log x) /
              (x ^ 2 * Real.log x ^ 2) := by gcongr
        _ = 3 * (M * s) / (x ^ 2 * Real.log x) := by
          field_simp [ne_of_gt hlogpos]
    have hfirst' :
        (M * s) / (x ^ 2 * Real.log x ^ 2) ≤
          2 * (M * s) / (x ^ 2 * Real.log x) := by
      have hone : 1 ≤ 2 * Real.log x := by linarith
      apply (div_le_div_iff₀ hden₂ hden₃).2
      nlinarith [mul_nonneg hMs hden₃.le]
    calc
      (M * s) / (x ^ 2 * Real.log x * Real.log z) +
          (M * s) * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2) ≤
          (M * s) / (x ^ 2 * Real.log x ^ 2) +
            3 * (M * s) / (x ^ 2 * Real.log x) :=
        add_le_add hfirst hsecond
      _ ≤ 2 * (M * s) / (x ^ 2 * Real.log x) +
            3 * (M * s) / (x ^ 2 * Real.log x) :=
        add_le_add hfirst' le_rfl
      _ = 5 * (M * s) / (x ^ 2 * Real.log x) := by ring
  rw [abs_mul]
  calc
    |firstMomentAbelDerivative s z x| * |thetaError x| ≤
        (5 * (M * s) / (x ^ 2 * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      exact mul_le_mul (hderiv.trans hsimplified) hTheta (abs_nonneg _)
        (div_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg hM hs.1)) (by positivity))
    _ ≤ mertensErrorMajorant (2 * C * (M * s)) x := by
      unfold mertensErrorMajorant
      have hCMs : 0 ≤ C * (M * s) :=
        mul_nonneg hC (mul_nonneg hM hs.1)
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]
      nlinarith

/-- Uniform Abel remainder for the first-moment kernel.  The factor `s` is
kept literal; it is never absorbed into a global compactness constant. -/
theorem abs_firstMomentWeightedAbelRemainder_le
    {C M s z : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder (firstMomentKernel s) z (A : ℝ) (Y : ℝ)| ≤
      6 * (C * M) * s / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hCMs : 0 ≤ C * (M * s) :=
    mul_nonneg hC (mul_nonneg hM hs.1)
  have hThetaCell : IntervalIntegrable
      (fun x : ℝ =>
        deriv (firstMomentAbelCoefficient s z) x * Chebyshev.theta x)
      volume (A : ℝ) (Y : ℝ) := by
    have hfull := intervalIntegrable_deriv_firstMoment_mul_theta
      hs hz hY hYz
    apply hfull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hMainInt : IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) :=
    intervalIntegrable_deriv_firstMoment_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hmajorInt : IntervalIntegrable
      (mertensErrorMajorant (2 * C * (M * s))) volume
      (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_mertensErrorMajorant (2 * C * (M * s))
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x|) ≤
        2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
    have habsInt : IntervalIntegrable
        (fun x : ℝ =>
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x|) volume (A : ℝ) (Y : ℝ) := by
      simpa only [firstMomentAbelCoefficient] using hErrorInt.abs
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x|) ≤
          ∫ x in (A : ℝ)..Y,
            mertensErrorMajorant (2 * C * (M * s)) x := by
        exact intervalIntegral.integral_mono_on hAYR habsInt hmajorInt
          (fun x hx => by
            have hx2 : 2 ≤ x := hAR.trans hx.1
            have hxz : x ≤ z := hx.2.trans hYz
            rw [show deriv
                (weightedAbelCoefficient (firstMomentKernel s) z) x =
                  firstMomentAbelDerivative s z x by
              simpa only [firstMomentAbelCoefficient] using
                deriv_firstMomentAbelCoefficient hs hz (by linarith) hxz]
            exact abs_firstMomentAbelDerivative_mul_thetaError_le
              hC hM hs hz hx2 hxz hPhi hPhiPrime (hTheta x hx))
      _ = mertensErrorPrimitive (2 * C * (M * s)) (Y : ℝ) -
          mertensErrorPrimitive (2 * C * (M * s)) (A : ℝ) :=
        integral_mertensErrorMajorant (2 * C * (M * s)) hAR hAYR
      _ ≤ 2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg :
            0 ≤ 2 * (C * (M * s)) / Real.log (Y : ℝ) ^ 3 := by
          positivity
        have heq :
            -(2 * C * (M * s)) / Real.log (Y : ℝ) ^ 3 -
                (-(2 * C * (M * s)) / Real.log (A : ℝ) ^ 3) =
              2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 -
                2 * (C * (M * s)) / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |firstMomentAbelCoefficient s z (A : ℝ)| *
          |thetaError (A : ℝ)| ≤
        C * (M * s) / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    exact abs_firstMomentAbelCoefficient_mul_thetaError_le hM hs hz hAR
      (hAYR.trans hYz) hPhi (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |firstMomentAbelCoefficient s z (Y : ℝ)| *
          |thetaError (Y : ℝ)| ≤
        C * (M * s) / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    calc
      |firstMomentAbelCoefficient s z (Y : ℝ) * thetaError (Y : ℝ)| ≤
          C * (M * s) / Real.log (Y : ℝ) ^ 4 := by
        exact abs_firstMomentAbelCoefficient_mul_thetaError_le hM hs hz
          (by exact_mod_cast hY) hYz hPhi
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
      _ ≤ C * (M * s) / Real.log (A : ℝ) ^ 4 := by
        have hlogYpos : 0 < Real.log (Y : ℝ) := by
          exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
        have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
          Real.log_le_log hApos hAYR
        gcongr
  have hinv4 :
      C * (M * s) / Real.log (A : ℝ) ^ 4 ≤
        2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
    have hone : 1 ≤ 2 * Real.log (A : ℝ) := by linarith
    have hpowNonneg : 0 ≤ Real.log (A : ℝ) ^ 3 :=
      pow_nonneg hlogApos.le 3
    have hmul := mul_le_mul_of_nonneg_right hone hpowNonneg
    have hinv :
        1 / Real.log (A : ℝ) ^ 4 ≤
          2 / Real.log (A : ℝ) ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hlogApos 4)
        (pow_pos hlogApos 3)).2
      calc
        1 * Real.log (A : ℝ) ^ 3 ≤
            (2 * Real.log (A : ℝ)) * Real.log (A : ℝ) ^ 3 := hmul
        _ = 2 * Real.log (A : ℝ) ^ 4 := by ring
    calc
      C * (M * s) / Real.log (A : ℝ) ^ 4 =
          (C * (M * s)) * (1 / Real.log (A : ℝ) ^ 4) := by ring
      _ ≤ (C * (M * s)) * (2 / Real.log (A : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hinv hCMs
      _ = 2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by ring
  calc
    |weightedAbelRemainder (firstMomentKernel s) z
        (A : ℝ) (Y : ℝ)| ≤
      |firstMomentAbelCoefficient s z (Y : ℝ)| * |thetaError (Y : ℝ)| +
        |firstMomentAbelCoefficient s z (A : ℝ)| * |thetaError (A : ℝ)| +
        ∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x| :=
      abs_weightedAbelRemainder_le (firstMomentKernel s) z hAYR
    _ ≤ C * (M * s) / Real.log (A : ℝ) ^ 4 +
        C * (M * s) / Real.log (A : ℝ) ^ 4 +
        2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
      linarith
    _ ≤ 6 * (C * M) * s / Real.log (A : ℝ) ^ 3 := by
      calc
        _ ≤ 2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 +
            2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 +
            2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 :=
          add_le_add (add_le_add hinv4 hinv4) le_rfl
        _ = 6 * (C * M) * s / Real.log (A : ℝ) ^ 3 := by ring























end Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

end

theorem solution :
∀ {C M s z : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) M →
      Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
        LT.lt.{0} (1 : Real) z →
          ∀ {A Y : Nat},
            LE.le.{0} (2 : Nat) A →
              LE.le.{0} A Y →
                LE.le.{0} (↑Y) z →
                  (∀ (u : Real),
                      Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) u →
                        ∀ (t : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                            LE.le.{0}
                              (abs.{0} (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel u t))
                              (HMul.hMul.{0, 0, 0} M u)) →
                    (∀ (u : Real),
                        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) u →
                          ∀ (t : Real),
                            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                              LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernelDerivative u
                                    t))
                                (HMul.hMul.{0, 0, 0} M u)) →
                      (∀ (x : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} ↑A ↑Y) x →
                            LE.le.{0} (abs.{0} (Erdos390.Full.PrimeBandQuadrature.thetaError x))
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C x)
                                (HPow.hPow.{0, 0, 0} (Real.log x) (3 : Nat)))) →
                        LE.le.{0}
                          (abs.{0}
                            (Erdos390.Full.KernelPrimeQuadrature.weightedAbelRemainder
                              (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel s) z ↑A ↑Y))
                          (HDiv.hDiv.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Real) (HMul.hMul.{0, 0, 0} C M)) s)
                            (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat))) := by
  exact @Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_firstMomentWeightedAbelRemainder_le
