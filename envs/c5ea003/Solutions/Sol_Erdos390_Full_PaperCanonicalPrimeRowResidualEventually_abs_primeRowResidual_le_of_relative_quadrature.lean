-- Prove2me | solution 1 for Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_primeRowResidual_le_of_relative_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:21:58.43248+00:00
-- url     : https://prove2.me/submissions/7a314da4-2356-4bbc-9237-2597cf40f6f0

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

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

/-- The Dickman averaging identity after translating the unit interval.
This is the analytic content of the total-mass constraint. -/
lemma integral_rho_U_sub_shift (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rho (U - s - t)) = (U - s) * rho (U - s) := by
  have hx1 : 1 ≤ U - s := by
    norm_num [U] at hs ⊢
    linarith [hs.2]
  have hx5 : U - s ≤ 5 := by
    norm_num [U] at hs ⊢
    linarith [hs.1]
  have havg := rho_average_eq (x := U - s) hx1 hx5
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) rho (U - s)
  rw [show U - s - 1 = (U - s) - 1 by ring] at havg
  rw [hcomp]
  simpa [sub_eq_add_neg, add_assoc] using havg.symm

/-- At zero shift the preceding formula gives the first Palm mass identity. -/
lemma integral_rho_U_sub :
    (∫ t in (0 : ℝ)..1, rho (U - t)) = U * rho U := by
  simpa using integral_rho_U_sub_shift 0 (by norm_num)

/-- The normalized one-point Dickman weight integrates to the conditioned
total `U`. -/
lemma integral_F : (∫ t in (0 : ℝ)..1, F t) = U := by
  unfold F
  have hconst :
      (∫ t in (0 : ℝ)..1, rho (U - t) / rho U) =
        (∫ t in (0 : ℝ)..1, rho (U - t)) / rho U := by
    exact intervalIntegral.integral_div (f := fun t : ℝ => rho (U - t))
      (a := (0 : ℝ)) (b := 1) (rho U)
  rw [hconst, integral_rho_U_sub]
  field_simp [rho_U_ne_zero]

/-- The shifted one-point Palm weight has the exact residual-mass moment. -/
lemma integral_F_shift (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, F (s + t)) = (U - s) * F s := by
  unfold F
  simp_rw [show ∀ t : ℝ, U - (s + t) = U - s - t by intro t; ring]
  have hconst :
      (∫ t in (0 : ℝ)..1, rho (U - s - t) / rho U) =
        (∫ t in (0 : ℝ)..1, rho (U - s - t)) / rho U := by
    exact intervalIntegral.integral_div
      (f := fun t : ℝ => rho (U - s - t))
      (a := (0 : ℝ)) (b := 1) (rho U)
  rw [hconst, integral_rho_U_sub_shift s hs]
  ring

/-- Integrating one variable of the covariance kernel yields exactly the
negative diagonal term required by the deterministic total constraint. -/
lemma integral_covarianceKernel (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, covarianceKernel s t) = -s * F s := by
  have hFint : IntervalIntegrable F volume 0 1 := by
    have hcont : Continuous F := by
      unfold F
      exact (continuous_rho.comp
        (continuous_const.sub continuous_id)).div_const (rho U)
    exact hcont.intervalIntegrable 0 1
  have hshift : IntervalIntegrable (fun t : ℝ => F (s + t)) volume 0 1 := by
    have hcont : Continuous (fun t : ℝ => F (s + t)) := by
      have hF : Continuous F := by
        unfold F
        exact (continuous_rho.comp
          (continuous_const.sub continuous_id)).div_const (rho U)
      exact hF.comp (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable 0 1
  change (∫ t in (0 : ℝ)..1, F (s + t) - F s * F t) = -s * F s
  rw [intervalIntegral.integral_sub hshift (hFint.const_mul (F s))]
  rw [integral_F_shift s hs, intervalIntegral.integral_const_mul, integral_F]
  ring







/-! ## Density-weighted Palm moments and covariance -/



lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/



















lemma covarianceKernelQuotient_eq_div {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (ht0 : t ≠ 0) :
    covarianceKernelQuotient s t = covarianceKernel s t / t := by
  apply (eq_div_iff ht0).2
  rw [mul_comm]
  exact mul_covarianceKernelQuotient_eq_kernel hs ht





























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













lemma continuous_covarianceKernel_left (s : ℝ) :
    Continuous (covarianceKernel s) := by
  exact continuous_covarianceKernel.comp
    (continuous_const.prodMk continuous_id)





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

/- Source module: Erdos390.Full.PoissonDickmanWeightedInverse -/
section


/-!
# A deterministic weighted `L∞` quotient inverse

After writing the Poisson--Dickman test as `f(t)=t q(t)`, the covariance
operator is a nonlocal graph Laplacian with continuous edge kernel
`-K(s,t)/s`.  Strict Dickman log-concavity makes this edge kernel uniformly
positive when the second endpoint ranges in one fixed interior interval,
including at the removable axis `s=0`.  A maximum/minimum argument then
controls the oscillation of `q` directly.  This gives the weighted quotient
inverse without assuming Fredholm theory or an inverse theorem.
-/

open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.PoissonDickmanWeightedInverse

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit PoissonDickmanDirichlet









/-! The strict four-point inequality with one endpoint allowed to equal one.
The proof repeats the already audited shifted-slope integral argument, but
uses only positivity (not strict upper bounds) for the endpoints. -/













/-! ## The weighted operator as a graph Laplacian -/









/-- The removable row-sum identity, including the axis by continuity. -/
theorem weightedKernel_rowSum (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    F s + (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s) = 0 := by
  let R : ℝ → ℝ := fun u =>
    F u + ∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u
  have hRcont : Continuous R := by
    dsimp only [R]
    apply continuous_F.add
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)
  have hzero : Ioc (0 : ℝ) 1 ⊆ R ⁻¹' ({0} : Set ℝ) := by
    intro u hu
    have hucc : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    change R u = 0
    dsimp only [R]
    have hInt :
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u) =
          (∫ t in (0 : ℝ)..1, covarianceKernel u t) / u := by
      calc
        (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t u) =
            ∫ t in (0 : ℝ)..1, covarianceKernel u t / u := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htcc : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
          change covarianceKernelQuotient t u = covarianceKernel u t / u
          rw [covarianceKernelQuotient_eq_div htcc hucc hu0,
            covarianceKernel_comm]
        _ = (∫ t in (0 : ℝ)..1, covarianceKernel u t) / u := by
          rw [intervalIntegral.integral_div]
    rw [hInt, integral_covarianceKernel u hucc]
    field_simp [hu0]
    ring
  have hclosed : IsClosed (R ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hRcont
  have hclosure := closure_minimal hzero hclosed
  rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at hclosure
  exact hclosure hs









end Erdos390.Full.PoissonDickmanWeightedInverse

end

/- Source module: Erdos390.Full.DoubleKernelPrimeQuadrature -/
section


/-!
# Double-index prime quadrature for the Poisson--Dickman kernel

This module performs the two prime-index quadratures needed in the
positive-cell part of Lemma 8.4.  The constants are chosen once, before the
kernel coordinate, ambient scale, or moving endpoints.  The moving-low-cell
estimates are kept for the next layer; no lower endpoint tending to zero is
hidden in the positive-cell theorem below.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.DoubleKernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature
open PoissonDickmanKernelBounds
open PositiveCellTransfer







lemma mem_intervalPrimes_iff {A Y p : ℕ} :
    p ∈ intervalPrimes A Y ↔ p.Prime ∧ A < p ∧ p ≤ Y := by
  unfold intervalPrimes
  rw [Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hpzero, hpY⟩, hpPrime⟩, hpNotA⟩
    refine ⟨hpPrime, ?_, hpY⟩
    by_contra hnot
    exact hpNotA ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpA, hpY⟩
    refine ⟨⟨⟨Nat.zero_le p, hpY⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hpzero, hpA'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpA') hpA

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

lemma primeCellOperator_eq_sum (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f : ℝ → ℝ) :
    primeCellOperator z A Y f =
      ∑ p ∈ intervalPrimes A Y,
        f (realLogCoordinate z (p : ℝ)) / (p : ℝ) := by
  have hsub := primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => f (realLogCoordinate z (p : ℝ)) / (p : ℝ))
  unfold primeCellOperator fullWeightedReciprocalSum intervalPrimes
  exact ((eq_sub_iff_add_eq).2 hsum).symm







































/-! ## Moving-low input cell -/































end Erdos390.Full.DoubleKernelPrimeQuadrature

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









































/-- The finite prime sum in the conjugated reference row is exactly the
weighted prime-cell sum for `firstMomentKernel`. -/
theorem sum_primeWeight_mul_primeKernel_eq_primeCell
    {n W : ℕ} (hWY : W ≤ yNat n)
    (p : PrimeIndex n W) :
    (∑ q : PrimeIndex n W,
        primeWeight n q * primeKernel n p q) =
      primeCellOperator (y n) W (yNat n)
        (firstMomentKernel (tPrime n p.1)) := by
  have hsets : intervalPrimes W (yNat n) = primeBand n W := by
    ext q
    rw [mem_intervalPrimes_iff, mem_primeBand]
  rw [primeCellOperator_eq_sum (y n) hWY, hsets]
  symm
  apply Finset.sum_bij
      (fun q hq => (⟨q, hq⟩ : PrimeIndex n W))
  · intro q hq
    simp only [Finset.mem_univ]
  · intro q₁ hq₁ q₂ hq₂ heq
    exact congrArg Subtype.val heq
  · intro q hq
    exact ⟨q.1, q.2, Subtype.ext rfl⟩
  · intro q hq
    unfold primeWeight primeKernel firstMomentKernel tPrime realLogCoordinate
    ring

lemma firstMomentKernel_div_eq_kernel
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    firstMomentKernel s t / t = covarianceKernel s t := by
  by_cases ht0 : t = 0
  · subst t
    have hzero := mul_covarianceKernelQuotient_eq_kernel hs
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    have hkzero : covarianceKernel s 0 = 0 := by
      simpa only [zero_mul] using hzero.symm
    unfold firstMomentKernel
    rw [hkzero]
    norm_num
  · unfold firstMomentKernel
    field_simp [ht0]

/-- Symmetry identifies the full continuum main term with the removable
quotient row. -/
theorem integral_covarianceKernel_eq_mul_quotient
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, covarianceKernel s t) =
      s * (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have htUnit : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  calc
    covarianceKernel s t = covarianceKernel t s := covarianceKernel_comm _ _
    _ = s * covarianceKernelQuotient t s :=
      (mul_covarianceKernelQuotient_eq_kernel htUnit hs).symm

theorem primeDiagonal_add_fullKernelIntegral_eq_zero
    {n W : ℕ} (hn : 1 < n) (p : PrimeIndex n W) :
    primeDiagonal n p +
        (∫ t in (0 : ℝ)..1,
          covarianceKernel (tPrime n p.1) t) = 0 := by
  have hs := tPrime_mem_unit hn p
  rw [integral_covarianceKernel_eq_mul_quotient _ hs]
  unfold primeDiagonal
  have hrow := PoissonDickmanWeightedInverse.weightedKernel_rowSum
    (tPrime n p.1) hs
  calc
    DickmanBasic.F (tPrime n p.1) * tPrime n p.1 +
        tPrime n p.1 *
          (∫ t in (0 : ℝ)..1,
            covarianceKernelQuotient t (tPrime n p.1)) =
      tPrime n p.1 *
        (DickmanBasic.F (tPrime n p.1) +
          ∫ t in (0 : ℝ)..1,
            covarianceKernelQuotient t (tPrime n p.1)) := by ring
    _ = 0 := by rw [hrow, mul_zero]

lemma abs_covarianceKernel_integral_le
    {C s a b : ℝ} (hC : 0 ≤ C)
    (hs : s ∈ Icc (0 : ℝ) 1) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hKernel : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t) :
    |∫ t in a..b, covarianceKernel s t| ≤ (C * s) * (b - a) := by
  have hCs : 0 ≤ C * s := mul_nonneg hC hs.1
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := C * s)
    (f := fun t : ℝ => covarianceKernel s t) (fun t ht => by
      have ht' : t ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
      have htUnit : t ∈ Icc (0 : ℝ) 1 :=
        ⟨ha.trans ht'.1, ht'.2.trans hb⟩
      rw [Real.norm_eq_abs]
      calc
        |covarianceKernel s t| ≤ C * s * t := hKernel s hs t htUnit
        _ ≤ C * s := mul_le_of_le_one_right hCs htUnit.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm



set_option maxHeartbeats 1200000 in
/-- Deterministic attachment of relative first-moment quadrature to the
literal finite prime row. -/
theorem abs_primeRowResidual_le_of_relative_quadrature
    {D C : ℝ} (hC : 0 ≤ C)
    {n W : ℕ} (hn : 1 < n) (hW2 : 2 ≤ W) (hWY : W ≤ yNat n)
    (hKernel : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t)
    (hquad : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator (y n) W (yNat n) (firstMomentKernel s) -
          (∫ t in realLogCoordinate (y n) (W : ℝ)..
            realLogCoordinate (y n) (yNat n : ℝ),
              firstMomentKernel s t / t)| ≤
        (D / Real.log (W : ℝ) ^ 3) * s)
    (p : PrimeIndex n W) :
    |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
      primeRowRelativeError D C n W * tPrime n p.1 := by
  let s : ℝ := tPrime n p.1
  let a : ℝ := realLogCoordinate (y n) (W : ℝ)
  let b : ℝ := realLogCoordinate (y n) (yNat n : ℝ)
  let primeMain : ℝ :=
    primeCellOperator (y n) W (yNat n) (firstMomentKernel s)
  let continuumMain : ℝ := ∫ t in a..b, covarianceKernel s t
  let lowTail : ℝ := ∫ t in (0 : ℝ)..a, covarianceKernel s t
  let topTail : ℝ := ∫ t in b..1, covarianceKernel s t
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hWNat : (W : ℝ) ≤ (yNat n : ℝ) := by exact_mod_cast hWY
  have hWOne : (1 : ℝ) ≤ W := by exact_mod_cast hW2.trans' (by omega)
  have hyNatOne : (1 : ℝ) ≤ yNat n := hWOne.trans hWNat
  have haUnit : a ∈ Icc (0 : ℝ) 1 := by
    dsimp only [a]
    exact realLogCoordinate_mem_unit hy hWOne (hWNat.trans hyNatY)
  have hbUnit : b ∈ Icc (0 : ℝ) 1 := by
    dsimp only [b]
    exact realLogCoordinate_mem_unit hy hyNatOne hyNatY
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact realLogCoordinate_mono_nat hy hW2 hWY
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    dsimp only [s]
    exact tPrime_mem_unit hn p
  have hcontinuum :
      (∫ t in a..b, firstMomentKernel s t / t) = continuumMain := by
    dsimp only [continuumMain]
    apply intervalIntegral.integral_congr
    intro t ht
    have htUnit : t ∈ Icc (0 : ℝ) 1 := by
      have ht' : t ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using ht
      exact ⟨haUnit.1.trans ht'.1, ht'.2.trans hbUnit.2⟩
    exact firstMomentKernel_div_eq_kernel hs htUnit
  have hPrime :
      |primeMain - continuumMain| ≤
        (D / Real.log (W : ℝ) ^ 3) * s := by
    dsimp only [primeMain]
    rw [← hcontinuum]
    exact hquad s hs
  have hLow : |lowTail| ≤ (C * s) * a := by
    dsimp only [lowTail]
    simpa only [sub_zero] using
      abs_covarianceKernel_integral_le hC hs haUnit.1 (by norm_num)
        haUnit.2 hKernel
  have hTop : |topTail| ≤ (C * s) * (1 - b) := by
    dsimp only [topTail]
    exact abs_covarianceKernel_integral_le hC hs hbUnit.2 hbUnit.1
      (by norm_num) hKernel
  have hsplit :
      (∫ t in (0 : ℝ)..1, covarianceKernel s t) =
        lowTail + continuumMain + topTail := by
    have hIntLow : IntervalIntegrable (covarianceKernel s) volume
        (0 : ℝ) a := (continuous_covarianceKernel_left s).intervalIntegrable _ _
    have hIntMid : IntervalIntegrable (covarianceKernel s) volume
        a b := (continuous_covarianceKernel_left s).intervalIntegrable _ _
    have hIntTop : IntervalIntegrable (covarianceKernel s) volume
        b 1 := (continuous_covarianceKernel_left s).intervalIntegrable _ _
    have hfirst := intervalIntegral.integral_add_adjacent_intervals
      hIntLow hIntMid
    have hsecond := intervalIntegral.integral_add_adjacent_intervals
      (hIntLow.trans hIntMid) hIntTop
    dsimp only [lowTail, continuumMain, topTail]
    linarith
  have hzero : primeDiagonal n p +
      (∫ t in (0 : ℝ)..1, covarianceKernel s t) = 0 := by
    simpa only [s] using primeDiagonal_add_fullKernelIntegral_eq_zero hn p
  have hrow :
      rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p =
        primeDiagonal n p + primeMain := by
    unfold rowResidual
    rw [sum_primeWeight_mul_primeKernel_eq_primeCell hWY p]
  have hdecomp :
      rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p =
        (primeMain - continuumMain) - lowTail - topTail := by
    rw [hrow]
    rw [hsplit] at hzero
    linarith
  rw [hdecomp]
  calc
    |(primeMain - continuumMain) - lowTail - topTail| ≤
        |primeMain - continuumMain| + |lowTail| + |topTail| := by
      have h₁ := abs_sub (primeMain - continuumMain) lowTail
      have h₂ := abs_sub ((primeMain - continuumMain) - lowTail) topTail
      linarith
    _ ≤ (D / Real.log (W : ℝ) ^ 3) * s +
        (C * s) * a + (C * s) * (1 - b) :=
      add_le_add (add_le_add hPrime hLow) hTop
    _ = primeRowRelativeError D C n W * tPrime n p.1 := by
      dsimp only [primeRowRelativeError, s, a, b]
      ring







end Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

end

theorem solution :
∀ {D C : Real},
  LE.le.{0} (0 : Real) C →
    ∀ {n W : Nat},
      LT.lt.{0} (1 : Nat) n →
        LE.le.{0} (2 : Nat) W →
          LE.le.{0} W (Erdos390.Full.ArithmeticModel.yNat n) →
            (∀ (u : Real),
                Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) u →
                  ∀ (t : Real),
                    Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                      LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel u t))
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C u) t)) →
              (∀ (s : Real),
                  Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.DoubleKernelPrimeQuadrature.primeCellOperator
                            (Erdos390.Full.ArithmeticModel.y n) W (Erdos390.Full.ArithmeticModel.yNat n)
                            (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel s))
                          (∫ (t : Real) in
                            Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate (Erdos390.Full.ArithmeticModel.y n)
                              ↑W..Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate
                              (Erdos390.Full.ArithmeticModel.y n) ↑(Erdos390.Full.ArithmeticModel.yNat n),
                            HDiv.hDiv.{0, 0, 0}
                              (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel s t) t)))
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} D (HPow.hPow.{0, 0, 0} (Real.log ↑W) (3 : Nat))) s)) →
                ∀ (p : Erdos390.Full.PrimeSquarefreeDirichletGeometry.PrimeIndex n W),
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.Full.FiniteAnchoredDirichletQuadratic.rowResidual.{0}
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight n)
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal n)
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel n) p))
                    (HMul.hMul.{0, 0, 0}
                      (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.primeRowRelativeError D C n W)
                      (Erdos390.Full.ArithmeticModel.tPrime n ↑p)) := by
  exact @Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_primeRowResidual_le_of_relative_quadrature
