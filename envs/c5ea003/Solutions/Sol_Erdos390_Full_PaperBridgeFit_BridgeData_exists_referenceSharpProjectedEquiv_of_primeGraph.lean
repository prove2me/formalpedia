-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_referenceSharpProjectedEquiv_of_primeGraph
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:18:31.238877+00:00
-- url     : https://prove2.me/submissions/6b276ce3-edba-4cfd-a9ee-ce360338c946

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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_referenceCenteringDiagonal_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_referenceCenteringKernel_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_referenceSharpRow_eq_primeGraph_add_errors
import Theorems.Thm_Erdos390_Full_SquarefreeReferenceOperatorIdentification_referenceBandRow_eq_rawOperator

/- Source module: Erdos390.Full.StableInverse -/
section


/-!
# Stable inversion under an operator perturbation

This is the quantitative finite-dimensional perturbation lemma needed after
the continuum inverse has been transferred to the arithmetic gauge space.
It does not assume invertibility of the perturbed operator.  Instead it
derives it from a proved inverse for the reference operator and an operator
error smaller than the reciprocal inverse bound.
-/

namespace Erdos390.Full

noncomputable section

namespace StableInverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]







theorem perturbedEquiv_apply
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (x : X) :
    perturbedEquiv A Ainv E C delta hC hsmall
      hleft hinv herror x = (A + E) x := by
  simp [perturbedEquiv]

theorem perturbed_inverse_bound_mul
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    (1 - C * delta) *
        ‖(perturbedEquiv A Ainv E C delta hC hsmall
          hleft hinv herror).symm y‖ ≤ C * ‖y‖ := by
  let e := perturbedEquiv A Ainv E C delta hC hsmall
    hleft hinv herror
  have hcontrol := reference_control A Ainv E C delta hC
    hleft hinv herror (e.symm y)
  have happ : (A + E) (e.symm y) = y := by
    rw [← perturbedEquiv_apply A Ainv E C delta hC hsmall
      hleft hinv herror]
    exact e.apply_symm_apply y
  simpa [e, happ] using hcontrol

theorem perturbed_inverse_bound
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    ‖(perturbedEquiv A Ainv E C delta hC hsmall
        hleft hinv herror).symm y‖ ≤
      (C / (1 - C * delta)) * ‖y‖ := by
  have hcoef : 0 < 1 - C * delta := sub_pos.mpr hsmall
  rw [show (C / (1 - C * delta)) * ‖y‖ =
      (C * ‖y‖) / (1 - C * delta) by ring]
  apply (le_div_iff₀ hcoef).2
  simpa [mul_comm] using
    perturbed_inverse_bound_mul A Ainv E C delta hC
      hsmall hleft hinv herror y

end StableInverse

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

/- Source module: Erdos390.Full.FiniteGraphStableInverse -/
section


/-!
# Stable inversion on the actual finite gauge

The graph edge geometry proved at the continuum level is turned here into a
linear equivalence on the *actual* weighted gauge.  Its inverse and inverse
bound are conclusions of the maximum/minimum theorem.  A sufficiently small
operator error is then transferred by `StableInverse`; the perturbed inverse
is never assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteGraphStableInverse

open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

































theorem referenceGraphInvCLM_left
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (q : GaugeSpace omega) :
    referenceGraphInvCLM edge anchor omega hedge hdom hkappa
      hanchorTotal homega homegaTotal
      (referenceGraphCLM edge anchor omega hedge hdom hkappa
        hanchorTotal homega homegaTotal q) = q := by
  exact (referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal).symm_apply_apply q

/-- Quantitative inverse bound derived from the graph maximum principle. -/
theorem referenceGraphInvCLM_bound
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (v : GaugeSpace omega) :
    ‖referenceGraphInvCLM edge anchor omega hedge hdom hkappa
        hanchorTotal homega homegaTotal v‖ ≤
      (4 / (kappa * ∑ j, anchor j)) * ‖v‖ := by
  let e := referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal
  let q : GaugeSpace omega := e.symm v
  have happ : e q = v := e.apply_symm_apply v
  have hgauge : ∑ i, omega i * (q : Band → ℝ) i = 0 := q.2
  have hprojected (i : Band) :
      |meanProjection omega (graphOperator edge (q : Band → ℝ)) i| ≤ ‖v‖ := by
    have hcoord :
        meanProjection omega (graphOperator edge (q : Band → ℝ)) i =
          (v : Band → ℝ) i := by
      have hi := congrArg (fun x : GaugeSpace omega => (x : Band → ℝ) i) happ
      simpa only [e, referenceGraphEquiv, projectedGraphLinearMap] using hi
    rw [hcoord, ← Real.norm_eq_abs]
    exact norm_le_pi_norm (v : Band → ℝ) i
  have hpoint := abs_le_of_gauge_projectedGraph_bound
    edge anchor omega (q : Band → ℝ)
    (kappa := kappa) (G := ‖v‖) hedge hdom hkappa hanchorTotal
    homega homegaTotal hgauge hprojected
  change ‖(q : Band → ℝ)‖ ≤
    (4 / (kappa * ∑ j, anchor j)) * ‖v‖
  have hconstant : 0 ≤ (4 / (kappa * ∑ j, anchor j)) * ‖v‖ := by
    positivity
  rw [pi_norm_le_iff_of_nonneg hconstant]
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(q : Band → ℝ) i| ≤
        4 * ‖v‖ / (kappa * ∑ j, anchor j) := hpoint i
    _ = (4 / (kappa * ∑ j, anchor j)) * ‖v‖ := by ring

/-- Stable inversion of an actual arithmetic-gauge operator from a proved
graph reference and an explicit operator error. -/
theorem exists_actualGaugeEquiv_of_graph_error
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa delta : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (actual : GaugeSpace omega →L[ℝ] GaugeSpace omega)
    (hsmall : (4 / (kappa * ∑ j, anchor j)) * delta < 1)
    (herror : ∀ q,
      ‖(actual - referenceGraphCLM edge anchor omega hedge hdom hkappa
        hanchorTotal homega homegaTotal) q‖ ≤ delta * ‖q‖) :
    ∃ actualEquiv : GaugeSpace omega ≃L[ℝ] GaugeSpace omega,
      (∀ q, actualEquiv q = actual q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        ((4 / (kappa * ∑ j, anchor j)) /
          (1 - (4 / (kappa * ∑ j, anchor j)) * delta)) * ‖v‖ := by
  let reference := referenceGraphCLM edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal
  let referenceInv := referenceGraphInvCLM edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal
  let E := actual - reference
  let C := 4 / (kappa * ∑ j, anchor j)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hleft : ∀ q, referenceInv (reference q) = q := by
    intro q
    exact referenceGraphInvCLM_left edge anchor omega hedge hdom hkappa
      hanchorTotal homega homegaTotal q
  have hinv : ∀ v, ‖referenceInv v‖ ≤ C * ‖v‖ := by
    intro v
    exact referenceGraphInvCLM_bound edge anchor omega hedge hdom hkappa
      hanchorTotal homega homegaTotal v
  have hE : ∀ q, ‖E q‖ ≤ delta * ‖q‖ := by
    simpa only [E, reference] using herror
  let actualEquiv := StableInverse.perturbedEquiv
    reference referenceInv E C delta hC hsmall hleft hinv hE
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [show actualEquiv q = (reference + E) q by
      exact StableInverse.perturbedEquiv_apply
        reference referenceInv E C delta hC hsmall hleft hinv hE q]
    simp only [E, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    abel
  · intro v
    exact StableInverse.perturbed_inverse_bound
      reference referenceInv E C delta hC hsmall hleft hinv hE v

end Erdos390.Full.FiniteGraphStableInverse

end

/- Source module: Erdos390.Full.CompressedArithmeticOperator -/
section


/-!
# The actual compressed arithmetic operator

This file packages the diagonal and double-kernel cells used in the
arithmetic bridge, performs the sharp conjugation, and proves the complete
row aggregation estimate.  The moving low row is not discarded: its
normalization is exactly the one provided by the proved normalized
quadrature modules.

No inverse or spectral gap is an input here.  The output is the explicit
operator error that is fed to the finite graph inverse and then to
`StableInverse`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.CompressedArithmeticOperator

open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]









/-! ## Endpoint-specialized arithmetic and continuum matrices -/















/-! ## Projection to the actual arithmetic gauge -/

/-- A positive weighted projection costs at most a factor two in the
pointwise norm.  This applies to the actual sharp weights
`H_j alpha_j^2`, including the moving low band. -/
theorem abs_meanProjection_sub_le
    (omega x y : Band → ℝ) (R : ℝ)
    (homega : ∀ j, 0 ≤ omega j)
    (hTotal : 0 < ∑ j, omega j)
    (hxy : ∀ j, |x j - y j| ≤ R)
    (i : Band) :
    |meanProjection omega x i - meanProjection omega y i| ≤ 2 * R := by
  have htotal0 : (∑ j, omega j) ≠ 0 := ne_of_gt hTotal
  have hmean : |weightedMean omega x - weightedMean omega y| ≤ R := by
    have hidentity :
        weightedMean omega x - weightedMean omega y =
          (∑ j, omega j * (x j - y j)) / ∑ j, omega j := by
      unfold weightedMean weightTotal
      have hsum :
          (∑ j, omega j * x j) - ∑ j, omega j * y j =
            ∑ j, omega j * (x j - y j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [show (∑ j, omega j * x j) / (∑ j, omega j) -
          (∑ j, omega j * y j) / (∑ j, omega j) =
          ((∑ j, omega j * x j) - ∑ j, omega j * y j) /
            (∑ j, omega j) by field_simp [htotal0] ]
      rw [hsum]
    rw [hidentity, abs_div, abs_of_pos hTotal]
    apply (div_le_iff₀ hTotal).2
    calc
      |∑ j, omega j * (x j - y j)| ≤
          ∑ j, |omega j * (x j - y j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, omega j * R := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (homega j)]
        exact mul_le_mul_of_nonneg_left (hxy j) (homega j)
      _ = R * ∑ j, omega j := by
        rw [← Finset.sum_mul]
        ring
  unfold meanProjection
  calc
    |(x i - weightedMean omega x) -
        (y i - weightedMean omega y)| =
    |(x i - y i) -
          (weightedMean omega x - weightedMean omega y)| := by ring
    _ = |(x i - y i) +
        (-(weightedMean omega x - weightedMean omega y))| := by
      rw [sub_eq_add_neg]
    _ ≤ |x i - y i| +
        |-(weightedMean omega x - weightedMean omega y)| := abs_add_le _ _
    _ = |x i - y i| +
        |weightedMean omega x - weightedMean omega y| := by rw [abs_neg]
    _ ≤ R + R := add_le_add (hxy i) hmean
    _ = 2 * R := by ring

end Erdos390.Full.CompressedArithmeticOperator

end

/- Source module: Erdos390.Full.MovingLowGaugeTransfer -/
section


/-!
# Moving-low arithmetic/continuum gauge transfer

This file isolates the normalization which is delicate at the moving low
cell.  An additive estimate for the arithmetic center is not enough because
the center itself tends to zero.  We first prove a quantitative relative
center estimate from separate estimates for `H` and `H * alpha`.  We then
write the sharp conjugate of the weighted gauge projection exactly and
compare two such projections through their normalized weights
`omega_j = H_j * alpha_j^2`.

No limiting mesh, covariance gap, or inverse is assumed in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.MovingLowGaugeTransfer

open Erdos390.Lemma84
open PositiveCellTransfer
open PrimeSums
open PrimeBandQuadrature
open MovingLowMomentQuadrature

section RelativeCenter

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : ArithmeticBandGeometry.Partition n W Band}









end RelativeCenter

section SharpProjection

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

















omit [Fintype Band] [DecidableEq Band] in
theorem sharpWeight_nonneg_of_mass_nonneg
    (H alpha : Band → ℝ) (hH : ∀ j, 0 ≤ H j) (j : Band) :
    0 ≤ sharpWeight H alpha j := by
  exact mul_nonneg (hH j) (sq_nonneg (alpha j))















end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

end

/- Source module: Erdos390.Full.SquarefreeReferenceOperatorIdentification -/
section


/-!
# Exact identification of the signed squarefree reference operator

The signed reference covariance used in the arithmetic part of paper
Lemma 8.4 is defined prime by prime in
`SquarefreeCovarianceReference`.  The moving-low inverse, on the other
hand, is proved for the endpoint matrix called `arithmeticDiagonal` plus
`arithmeticKernel`.  This file proves that these are literally the same
finite operator for every certified prime partition.  No limit, row bound,
covariance estimate, or inverse is assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.SquarefreeReferenceOperatorIdentification

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PositiveCellTransfer
open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open CompressedArithmeticOperator
open ConditionedPoissonLimit DickmanBasic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : Partition n W Band}













/-- After the exact centre conjugation, the reference sharp row is exactly
the canonical arithmetic sharp operator used by the inverse theorem. -/
theorem referenceSharpRow_eq_arithmeticSharpOperator
    (E : IntervalCertificate P) (q : Band → ℝ) (i : Band)
    (hcenter : P.center i ≠ 0) :
    referenceSharpRow P q i =
      arithmeticSharpOperator (y n) E.lower E.upper P.center q i := by
  unfold referenceSharpRow arithmeticSharpOperator
  rw [referenceBandRow_eq_rawOperator E]
  unfold PaperWeightedInverseExport.rawOperator sharpOperator
  apply (div_eq_iff hcenter).2
  simp only
  rw [add_mul, Finset.sum_mul]
  apply congrArg₂ (fun x y : ℝ ↦ x + y)
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    field_simp [hcenter]

section MarkedProfileApplication

variable {Cell : Type*} [Fintype Cell]
variable {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
variable {M : ℕ}



end MarkedProfileApplication

end Erdos390.Full.SquarefreeReferenceOperatorIdentification

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





theorem tPrime_mem_unit (hn : 1 < n) (p : PrimeIndex n W) :
    tPrime n p.1 ∈ Icc (0 : ℝ) 1 :=
  ⟨(tPrime_pos hn p).le,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn p.2⟩





















end Erdos390.Full.PrimeSquarefreeDirichletGeometry

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

/- Source module: Erdos390.Full.PaperReferenceSharpPrimeGraph -/
section


/-!
# Prime-graph model for the literal sharp reference band operator

The endpoint double-quadrature route loses a factor depending on the first
cell width.  This file instead performs the comparison before band
quadrature.  A band coefficient `alpha_j x_j` is split exactly as

`t_p x_j + (alpha_j - t_p) x_j`.

The first term is a compression of the literal finite prime graph.  The
second is controlled by exact arithmetic centering.  Consequently the
constants below do not involve a least band centre, the number of bands, or
the low-cell width.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic FiniteGraphQuotientInverse
open ConditionedPoissonLimit DickmanBasic
open PoissonDickmanDirichlet
open PaperCanonicalSlowKappa

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- Exact first-moment identity on an actual arithmetic fiber. -/
theorem fiber_primeWeight_sum_eq_mass_mul_center (i : Band) :
    (∑ p ∈ B.partition.data.fiber i,
      primeWeight B.sampleData.n p) =
        B.harmonicMass i * B.bandCenter i := by
  change (∑ p ∈ B.partition.data.fiber i,
      tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = _
  have h : (∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        B.harmonicMass i * B.bandCenter i := by
    unfold harmonicMass bandCenter
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass i *
        ((∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass i)
    field_simp [ne_of_gt (B.partition.data.mass_pos i)]
  calc
    (∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 / (p.1 : ℝ)) =
        ∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = B.harmonicMass i * B.bandCenter i := h







/-- Compression preserves the whole literal prime-anchor mass exactly. -/
theorem sum_compressedPrimeAnchor_eq_anchorMass
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W)) :
    (∑ j : Band, B.compressedPrimeAnchor anchor j) =
      anchorMass (primeWeight B.sampleData.n) anchor := by
  classical
  unfold compressedPrimeAnchor anchorMass
  change (∑ j : Band,
      ∑ q ∈ Finset.univ.filter (fun q : BandPrime B.sampleData.n
        B.sampleData.W ↦ B.partition.band q = j),
        if q ∈ anchor then primeWeight B.sampleData.n q else 0) = _
  rw [Finset.sum_fiberwise Finset.univ B.partition.band
    (fun q : BandPrime B.sampleData.n B.sampleData.W ↦
      if q ∈ anchor then primeWeight B.sampleData.n q else 0)]
  simp

/-- Every compressed prime-graph edge is nonnegative. -/
theorem compressedPrimeGraphEdge_nonneg (i j : Band) :
    0 ≤ B.compressedPrimeGraphEdge i j := by
  have hnorm : 0 ≤
      1 / (B.harmonicMass i * B.bandCenter i) :=
    (one_div_pos.mpr
      (mul_pos (B.harmonicMass_pos i) (B.bandCenter_pos i))).le
  unfold compressedPrimeGraphEdge
  apply mul_nonneg hnorm
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  have hpcast : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hkernel : 0 ≤ -primeKernel B.sampleData.n p q := by
    exact neg_nonneg.mpr
      (covarianceKernel_nonpos
        (tPrime_mem_unit B.n_gt_one p)
        (tPrime_mem_unit B.n_gt_one q))
  exact mul_nonneg
    (mul_nonneg (one_div_nonneg.mpr hpcast.le)
      (primeWeight_pos B.n_gt_one q).le) hkernel

/-- The fixed continuum quotient gap gives an exact primewise edge gap
against every literal prime in the compact anchor block. -/
theorem canonicalSlowKappa_mul_tPrime_le_neg_primeKernel
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ q ∈ anchor,
      tPrime B.sampleData.n q.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (p : BandPrime B.sampleData.n B.sampleData.W)
    (q : BandPrime B.sampleData.n B.sampleData.W) (hq : q ∈ anchor) :
    canonicalSlowKappa * tPrime B.sampleData.n p.1 ≤
      -primeKernel B.sampleData.n p q := by
  have hgap := canonicalSlowKappa_gap
    (tPrime B.sampleData.n p.1) (tPrime_mem_unit B.n_gt_one p)
    (tPrime B.sampleData.n q.1) (hinterior q hq)
  have hmul := mul_covarianceKernelQuotient_eq_kernel
    (s := tPrime B.sampleData.n q.1)
    (t := tPrime B.sampleData.n p.1)
    (tPrime_mem_unit B.n_gt_one q)
    (tPrime_mem_unit B.n_gt_one p)
  unfold primeKernel
  rw [covarianceKernel_comm]
  nlinarith [B.bandPrime_tPrime_pos p]

/-- The compressed finite prime graph sees the compressed anchor with the
same fixed gap.  No mesh width or minimum band centre occurs. -/
theorem canonicalSlowKappa_mul_compressedPrimeAnchor_le_edge
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ q ∈ anchor,
      tPrime B.sampleData.n q.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (i j : Band) :
    canonicalSlowKappa * B.compressedPrimeAnchor anchor j ≤
      B.compressedPrimeGraphEdge i j := by
  let A : ℝ := B.harmonicMass i * B.bandCenter i
  have hA : 0 < A := by
    exact mul_pos (B.harmonicMass_pos i) (B.bandCenter_pos i)
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W)
      (hp : p ∈ B.partition.data.fiber i) :
      canonicalSlowKappa * primeWeight B.sampleData.n p *
          B.compressedPrimeAnchor anchor j ≤
        ∑ q ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
            (-primeKernel B.sampleData.n p q) := by
    unfold compressedPrimeAnchor
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    by_cases hqa : q ∈ anchor
    · rw [if_pos hqa]
      have hgap := B.canonicalSlowKappa_mul_tPrime_le_neg_primeKernel
        anchor hinterior p q hqa
      have hfactor : 0 ≤
          (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q := by
        exact mul_nonneg (by positivity) (primeWeight_pos B.n_gt_one q).le
      have hscaled := mul_le_mul_of_nonneg_left hgap hfactor
      unfold primeWeight at hscaled ⊢
      ring_nf at hscaled ⊢
      exact hscaled
    · rw [if_neg hqa]
      have hkernel : 0 ≤ -primeKernel B.sampleData.n p q := by
        exact neg_nonneg.mpr
          (covarianceKernel_nonpos
            (tPrime_mem_unit B.n_gt_one p)
            (tPrime_mem_unit B.n_gt_one q))
      simp only [mul_zero]
      exact mul_nonneg
        (mul_nonneg (by positivity) (primeWeight_pos B.n_gt_one q).le)
        hkernel
  have hsum :
      canonicalSlowKappa * A * B.compressedPrimeAnchor anchor j ≤
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
              (-primeKernel B.sampleData.n p q) := by
    calc
      canonicalSlowKappa * A * B.compressedPrimeAnchor anchor j =
          ∑ p ∈ B.partition.data.fiber i,
            canonicalSlowKappa * primeWeight B.sampleData.n p *
              B.compressedPrimeAnchor anchor j := by
        rw [← Finset.sum_mul]
        rw [← Finset.mul_sum]
        rw [B.fiber_primeWeight_sum_eq_mass_mul_center]
      _ ≤ _ := Finset.sum_le_sum fun p hp ↦ hinner p hp
  unfold compressedPrimeGraphEdge
  calc
    canonicalSlowKappa * B.compressedPrimeAnchor anchor j =
        (1 / A) *
          (canonicalSlowKappa * A * B.compressedPrimeAnchor anchor j) := by
      field_simp [ne_of_gt hA]
    _ ≤ (1 / A) *
        (∑ p ∈ B.partition.data.fiber i,
          ∑ q ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
              (-primeKernel B.sampleData.n p q)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rfl

/-- A relative literal prime-row defect remains relative after sharp band
compression, including in the moving low band. -/
theorem abs_referenceResidualError_le
    {rowError R : ℝ} (hrowError : 0 ≤ rowError)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |B.referenceResidualError x i| ≤ rowError * R := by
  let A : ℝ := B.harmonicMass i * B.bandCenter i
  have hA : 0 < A :=
    mul_pos (B.harmonicMass_pos i) (B.bandCenter_pos i)
  have hterm (p : BandPrime B.sampleData.n B.sampleData.W) :
      |(1 / (p.1 : ℝ)) *
          rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p * x i| ≤
        (rowError * R) * primeWeight B.sampleData.n p := by
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hinv : 0 ≤ 1 / (p.1 : ℝ) := one_div_nonneg.mpr hp.le
    have hfirst := mul_le_mul_of_nonneg_left (hrow p) hinv
    have hfirstUpperNonneg : 0 ≤
        (1 / (p.1 : ℝ)) *
          (rowError * tPrime B.sampleData.n p.1) :=
      mul_nonneg hinv
        (mul_nonneg hrowError (B.bandPrime_tPrime_pos p).le)
    have hscaled := mul_le_mul hfirst (hx i) (abs_nonneg _)
      hfirstUpperNonneg
    unfold primeWeight
    calc
      |(1 / (p.1 : ℝ)) *
          rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p * x i| =
        (1 / (p.1 : ℝ)) *
          |rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p| * |x i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hinv]
      _ ≤
        ((1 / (p.1 : ℝ)) *
          (rowError * tPrime B.sampleData.n p.1)) * R := hscaled
      _ = (rowError * R) *
          (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) := by ring
  unfold referenceResidualError
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hA)]
  calc
    (1 / A) *
        |∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i| ≤
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          |(1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (one_div_nonneg.mpr hA.le)
    _ ≤ (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          (rowError * R) * primeWeight B.sampleData.n p := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
      exact Finset.sum_le_sum fun p hp ↦ hterm p
    _ = rowError * R := by
      rw [← Finset.mul_sum, B.fiber_primeWeight_sum_eq_mass_mul_center]
      dsimp only [A]
      field_simp [ne_of_gt (B.harmonicMass_pos i),
        ne_of_gt (B.bandCenter_pos i)]





/-- The literal reference sharp row is uniformly close, in the sharp row
normalization, to the compressed prime graph.  Crucially, the right-hand
side contains no inverse power of the moving low-band center. -/
theorem abs_referenceSharpRow_sub_primeGraph_le
    {rowError w CF CKernel R : ℝ}
    (hrowError : 0 ≤ rowError) (hw : 0 ≤ w)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |referenceSharpRow B.partition x i -
        graphOperator B.compressedPrimeGraphEdge x i| ≤
      (rowError + (2 * CF + 7 * CKernel) * w) * R := by
  have hres := B.abs_referenceResidualError_le
    hrowError hrow x hx i
  have hdiag := B.abs_referenceCenteringDiagonal_le
    hw hCF hR hFdiff hdevSup x hx i
  have hkernel := B.abs_referenceCenteringKernel_le
    hCKernel hR hKernelFirst hdevL1 x hx i
  rw [B.referenceSharpRow_eq_primeGraph_add_errors]
  calc
    |graphOperator B.compressedPrimeGraphEdge x i +
          B.referenceResidualError x i +
          B.referenceCenteringDiagonal x i +
          B.referenceCenteringKernel x i -
        graphOperator B.compressedPrimeGraphEdge x i| =
        |B.referenceResidualError x i +
          B.referenceCenteringDiagonal x i +
          B.referenceCenteringKernel x i| := by
            congr 1
            ring
    _ ≤ |B.referenceResidualError x i| +
          |B.referenceCenteringDiagonal x i| +
          |B.referenceCenteringKernel x i| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ rowError * R + 2 * CF * w * R + 7 * CKernel * w * R :=
      add_le_add (add_le_add hres hdiag) hkernel
    _ = (rowError + (2 * CF + 7 * CKernel) * w) * R := by ring

/-- Stable inversion of the literal arithmetic reference sharp operator by
the compressed prime graph.  The error and inverse constants depend only on
the prime-row residual and the two structural continuum constants; neither
the number of bands nor the least arithmetic centre occurs. -/
theorem exists_referenceSharpProjectedEquiv_of_primeGraph
    (cert : PositiveCellTransfer.IntervalCertificate B.partition)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ q ∈ anchor,
      tPrime B.sampleData.n q.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    {rowError w CF CKernel : ℝ}
    (hrowError : 0 ≤ rowError) (hw : 0 ≤ w)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (hanchorMass : 0 <
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hsmall :
      (4 / (canonicalSlowKappa *
          anchorMass (primeWeight B.sampleData.n) anchor)) *
        (2 * (rowError + (2 * CF + 7 * CKernel) * w)) < 1) :
    ∃ referenceEquiv :
        PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center ≃L[ℝ]
          PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center,
      (∀ q, referenceEquiv q =
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center
          (MovingLowGaugeTransfer.sharpWeight
            B.partition.mass B.partition.center)
          (ne_of_gt B.actualSharpWeightTotal_pos) q) ∧
      ∀ v, ‖referenceEquiv.symm v‖ ≤
        ((4 / (canonicalSlowKappa *
            anchorMass (primeWeight B.sampleData.n) anchor)) /
          (1 - (4 / (canonicalSlowKappa *
              anchorMass (primeWeight B.sampleData.n) anchor)) *
            (2 * (rowError + (2 * CF + 7 * CKernel) * w)))) * ‖v‖ := by
  letI : Nonempty Band := ⟨B.lowBand⟩
  let omega : Band → ℝ := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let err : ℝ := rowError + (2 * CF + 7 * CKernel) * w
  let delta : ℝ := 2 * err
  let actual : FiniteGraphStableInverse.GaugeSpace omega →L[ℝ]
      FiniteGraphStableInverse.GaugeSpace omega :=
    ArithmeticGaugeStableInverse.projectedSharpCLM
      (CompressedArithmeticOperator.arithmeticDiagonal
        (y B.sampleData.n) cert.lower cert.upper)
      (CompressedArithmeticOperator.arithmeticKernel
        (y B.sampleData.n) cert.lower cert.upper)
      B.partition.center omega (ne_of_gt B.actualSharpWeightTotal_pos)
  have homega : ∀ i, 0 ≤ omega i := fun i ↦
    MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
      B.partition.mass B.partition.center
      (fun j ↦ (B.partition.data.mass_pos j).le) i
  have homegaTotal : 0 < ∑ i, omega i := by
    simpa only [omega, MovingLowGaugeTransfer.sharpWeightTotal] using
      B.actualSharpWeightTotal_pos
  have hedge : ∀ i j, 0 ≤ B.compressedPrimeGraphEdge i j :=
    B.compressedPrimeGraphEdge_nonneg
  have hdom : ∀ i j,
      canonicalSlowKappa * B.compressedPrimeAnchor anchor j ≤
        B.compressedPrimeGraphEdge i j :=
    B.canonicalSlowKappa_mul_compressedPrimeAnchor_le_edge anchor hinterior
  have hanchorTotal :
      0 < ∑ j, B.compressedPrimeAnchor anchor j := by
    rw [B.sum_compressedPrimeAnchor_eq_anchorMass]
    exact hanchorMass
  have herrNonneg : 0 ≤ err := by
    dsimp only [err]
    positivity
  have hdeltaNonneg : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hstableSmall :
      (4 / (canonicalSlowKappa *
          ∑ j, B.compressedPrimeAnchor anchor j)) * delta < 1 := by
    simpa only [delta, err, B.sum_compressedPrimeAnchor_eq_anchorMass]
      using hsmall
  have herror : ∀ q,
      ‖(actual - FiniteGraphStableInverse.referenceGraphCLM
        B.compressedPrimeGraphEdge (B.compressedPrimeAnchor anchor) omega
        hedge hdom canonicalSlowKappa_pos hanchorTotal homega
          homegaTotal) q‖ ≤ delta * ‖q‖ := by
    intro q
    have hraw (i : Band) :
        |CompressedArithmeticOperator.arithmeticSharpOperator
              (y B.sampleData.n) cert.lower cert.upper
              B.partition.center (q : Band → ℝ) i -
            graphOperator B.compressedPrimeGraphEdge
              (q : Band → ℝ) i| ≤ err * ‖q‖ := by
      have href := B.abs_referenceSharpRow_sub_primeGraph_le
        hrowError hw hCF hCKernel (norm_nonneg q) hrow hFdiff
        hKernelFirst hdevSup hdevL1 (q : Band → ℝ)
        (fun j ↦ by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (q : Band → ℝ) j) i
      rw [referenceSharpRow_eq_arithmeticSharpOperator cert
        (q : Band → ℝ) i
        (ne_of_gt (B.partition.center_pos B.n_gt_one i))] at href
      simpa only [err] using href
    have hprojected (i : Band) :
        |meanProjection omega
              (fun j ↦ CompressedArithmeticOperator.arithmeticSharpOperator
                (y B.sampleData.n) cert.lower cert.upper
                B.partition.center (q : Band → ℝ) j) i -
            meanProjection omega
              (graphOperator B.compressedPrimeGraphEdge
                (q : Band → ℝ)) i| ≤
          2 * (err * ‖q‖) :=
      CompressedArithmeticOperator.abs_meanProjection_sub_le omega
        (fun j ↦ CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
          B.partition.center (q : Band → ℝ) j)
        (graphOperator B.compressedPrimeGraphEdge (q : Band → ℝ))
        (err * ‖q‖) homega homegaTotal hraw i
    have hnonneg : 0 ≤ delta * ‖q‖ :=
      mul_nonneg hdeltaNonneg (norm_nonneg q)
    change ‖(((actual - FiniteGraphStableInverse.referenceGraphCLM
        B.compressedPrimeGraphEdge (B.compressedPrimeAnchor anchor) omega
        hedge hdom canonicalSlowKappa_pos hanchorTotal homega
          homegaTotal) q :
        FiniteGraphStableInverse.GaugeSpace omega) : Band → ℝ)‖ ≤
      delta * ‖q‖
    rw [pi_norm_le_iff_of_nonneg hnonneg]
    intro i
    rw [Real.norm_eq_abs]
    change |meanProjection omega
          (fun j ↦ CompressedArithmeticOperator.arithmeticSharpOperator
            (y B.sampleData.n) cert.lower cert.upper
            B.partition.center (q : Band → ℝ) j) i -
        meanProjection omega
          (graphOperator B.compressedPrimeGraphEdge
            (q : Band → ℝ)) i| ≤ delta * ‖q‖
    exact (hprojected i).trans_eq (by simp only [delta]; ring)
  obtain ⟨referenceEquiv, hreference, hinv⟩ :=
    FiniteGraphStableInverse.exists_actualGaugeEquiv_of_graph_error
      B.compressedPrimeGraphEdge (B.compressedPrimeAnchor anchor) omega
      hedge hdom canonicalSlowKappa_pos hanchorTotal homega homegaTotal
      actual hstableSmall herror
  refine ⟨referenceEquiv, ?_, ?_⟩
  · intro q
    simpa only [actual, omega] using hreference q
  · intro v
    simpa only [delta, err, B.sum_compressedPrimeAnchor_eq_anchorMass]
      using hinv v



end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  (cert :
    Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_2}
      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
  (anchor :
    Finset.{0}
      (Erdos390.Full.ArithmeticBandGeometry.BandPrime
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))),
  (∀
      (q :
        Erdos390.Full.ArithmeticBandGeometry.BandPrime
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
      Membership.mem.{0, 0} anchor q →
        Membership.mem.{0, 0} (Set.Icc.{0} (1 / 8 : Real) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real)))
          (Erdos390.Full.ArithmeticModel.tPrime
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
            (↑q : Nat))) →
    ∀ {rowError w CF CKernel : Real},
      LE.le.{0} (0 : Real) rowError →
        LE.le.{0} (0 : Real) w →
          LE.le.{0} (0 : Real) CF →
            LE.le.{0} (0 : Real) CKernel →
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
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        p))
                    (HMul.hMul.{0, 0, 0} rowError
                      (Erdos390.Full.ArithmeticModel.tPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        (↑p : Nat)))) →
                (∀
                    (p :
                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.DickmanBasic.F
                            (Erdos390.Full.ArithmeticModel.tPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (↑p : Nat)))
                          (Erdos390.Full.DickmanBasic.F
                            (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B
                              (Erdos390.Full.ArithmeticBandGeometry.Partition.band.{u_2}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p)))))
                      (HMul.hMul.{0, 0, 0} CF
                        (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)))) →
                  (∀
                      (p q :
                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                      LE.le.{0}
                        (abs.{0}
                          (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                            (Erdos390.Full.ArithmeticModel.tPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (↑p : Nat))
                            (Erdos390.Full.ArithmeticModel.tPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (↑q : Nat))))
                        (HMul.hMul.{0, 0, 0} CKernel
                          (Erdos390.Full.ArithmeticModel.tPrime
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (↑p : Nat)))) →
                    (∀
                        (p :
                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                        LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)) w) →
                      LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
                          (HMul.hMul.{0, 0, 0} (7 : Real) w) →
                        LT.lt.{0} (0 : Real)
                            (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                              (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                              anchor) →
                          LT.lt.{0}
                              (HMul.hMul.{0, 0, 0}
                                (HDiv.hDiv.{0, 0, 0} (4 : Real)
                                  (HMul.hMul.{0, 0, 0} Erdos390.Full.PaperCanonicalSlowKappa.canonicalSlowKappa
                                    (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                      anchor)))
                                (HMul.hMul.{0, 0, 0} (2 : Real)
                                  (HAdd.hAdd.{0, 0, 0} rowError
                                    (HMul.hMul.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) CF)
                                        (HMul.hMul.{0, 0, 0} (7 : Real) CKernel))
                                      w))))
                              (1 : Real) →
                            ∃ (referenceEquiv :
                              ContinuousLinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                              And
                                (∀
                                  (q :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                  Eq.{u_2 + 1}
                                    ((referenceEquiv :
                                        ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                      q)
                                    ((Erdos390.Full.ArithmeticGaugeStableInverse.projectedSharpCLM.{u_2}
                                          (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_2}
                                            (Erdos390.Full.ArithmeticModel.y
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                                          (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_2}
                                            (Erdos390.Full.ArithmeticModel.y
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                                          (ne_of_gt.{0}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualSharpWeightTotal_pos.{u_1,
                                                u_2}
                                              B)) :
                                        ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{u_2}
                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))) →
                                          ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{u_2}
                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))))
                                      q))
                                (∀
                                  (v :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                  LE.le.{0}
                                    (Norm.norm.{u_2}
                                      ((ContinuousLinearEquiv.symm.{0, 0, u_2, u_2} referenceEquiv :
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                            ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                        v))
                                    (HMul.hMul.{0, 0, 0}
                                      (HDiv.hDiv.{0, 0, 0}
                                        (HDiv.hDiv.{0, 0, 0} (4 : Real)
                                          (HMul.hMul.{0, 0, 0} Erdos390.Full.PaperCanonicalSlowKappa.canonicalSlowKappa
                                            (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                              (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                              anchor)))
                                        (HSub.hSub.{0, 0, 0} (1 : Real)
                                          (HMul.hMul.{0, 0, 0}
                                            (HDiv.hDiv.{0, 0, 0} (4 : Real)
                                              (HMul.hMul.{0, 0, 0}
                                                Erdos390.Full.PaperCanonicalSlowKappa.canonicalSlowKappa
                                                (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                                  (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)))
                                                  anchor)))
                                            (HMul.hMul.{0, 0, 0} (2 : Real)
                                              (HAdd.hAdd.{0, 0, 0} rowError
                                                (HMul.hMul.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) CF)
                                                    (HMul.hMul.{0, 0, 0} (7 : Real) CKernel))
                                                  w))))))
                                      (Norm.norm.{u_2} v))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_referenceSharpProjectedEquiv_of_primeGraph
