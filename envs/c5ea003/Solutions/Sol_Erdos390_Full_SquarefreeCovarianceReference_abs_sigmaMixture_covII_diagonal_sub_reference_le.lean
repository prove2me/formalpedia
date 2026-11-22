-- Prove2me | solution 1 for Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_diagonal_sub_reference_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:30:30.403373+00:00
-- url     : https://prove2.me/submissions/696ced74-7c66-47e6-8f10-05950c0a1fb2

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

/- Source module: Erdos390.Full.ArithmeticModel -/
section


/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel















































theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]























































end Erdos390.Full.ArithmeticModel

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















/-! ## The common paper-scale main term -/

















/-- Four marks keep the paper coordinate inside the range on which the
constructed Dickman function is positive. -/
theorem paperDivisorCoordinate_mem_zero_five {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisorCoordinate n d ∧ paperDivisorCoordinate n d ≤ 5 := by
  have hnpos : 0 < n := by omega
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hyNatPos : 0 < yNat n := by
    by_contra hnot
    have hyNat0 : yNat n = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hyNat0] at hd4
    omega
  have hyNatRpos : (0 : ℝ) < (yNat n : ℝ) := by exact_mod_cast hyNatPos
  have hdCast : (d : ℝ) ≤ (yNat n : ℝ) ^ 4 := by exact_mod_cast hd4
  have hlogdNat : Real.log (d : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hdR hdCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogdY : Real.log (d : ℝ) ≤ 4 * Real.log (y n) := by
    calc
      Real.log (d : ℝ) ≤ 4 * Real.log (yNat n : ℝ) := hlogdNat
      _ ≤ 4 * Real.log (y n) := by linarith
  have hquot0 : 0 ≤ Real.log (d : ℝ) / Real.log (y n) :=
    div_nonneg hlogd0 hylog.le
  have hquot4 : Real.log (d : ℝ) / Real.log (y n) ≤ 4 :=
    (div_le_iff₀ hylog).2 (by simpa using hlogdY)
  unfold paperDivisorCoordinate DickmanBasic.U
  constructor <;> linarith

theorem paperDivisibilityMain_nonneg_le {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisibilityMain n d ∧
      paperDivisibilityMain n d ≤
        1 / (rho DickmanBasic.U * (d : ℝ)) := by
  have hv := paperDivisorCoordinate_mem_zero_five hn hd hd4
  have hrv : 0 < rho (paperDivisorCoordinate n d) :=
    rho_pos_on_zero_five hv.1 hv.2
  have hrv1 : rho (paperDivisorCoordinate n d) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hv.2
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold paperDivisibilityMain
  constructor
  · positivity
  · rw [div_div]
    exact div_le_div_of_nonneg_right hrv1 (mul_pos hrU hdR).le



















/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.FiniteProbabilityMixture -/
section


/-!
# Exact finite tagged probability mixtures

The covariance of a mixture is not the mixture of the covariances.  This
module therefore starts one level lower: expectations on a tagged sigma
type are proved to be exact convex combinations.  Common-profile estimates
can then be averaged before any covariance subtraction is performed.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]





/-- A common centered expectation error survives an arbitrary convex
mixture with exactly the same error. -/
theorem abs_sigmaMixture_expect_sub_common_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) (main error : ℝ)
    (hcell : ∀ c,
      |(mu c).expect (fun x ↦ F ⟨c, x⟩) - main| ≤ error) :
    |(sigmaMixture weight mu).expect F - main| ≤ error := by
  rw [sigmaMixture_expect]
  have hrewrite :
      (∑ c, weight.mass c * (mu c).expect (fun x ↦ F ⟨c, x⟩)) -
          main =
        ∑ c, weight.mass c *
          ((mu c).expect (fun x ↦ F ⟨c, x⟩) - main) := by
    calc
      _ = (∑ c, weight.mass c *
            (mu c).expect (fun x ↦ F ⟨c, x⟩)) -
          (∑ c, weight.mass c) * main := by rw [weight.mass_sum, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c hc
        ring
  rw [hrewrite]
  calc
    |∑ c, weight.mass c *
        ((mu c).expect (fun x ↦ F ⟨c, x⟩) - main)| ≤
        ∑ c, |weight.mass c *
          ((mu c).expect (fun x ↦ F ⟨c, x⟩) - main)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, weight.mass c * error := by
      apply Finset.sum_le_sum
      intro c hc
      rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = error := by
      rw [← Finset.sum_mul, weight.mass_sum, one_mul]



end FiniteProbability

namespace PrimePowerCovariance.BoundedValuationLaw

open ArithmeticModel

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}















/-- Divisibility probabilities of the tagged law inherit a common profile
estimate before covariance is formed.  This is the step which accounts for
the between-cell covariance term: it is deliberately an expectation
statement, not an average-of-covariances statement. -/
theorem abs_sigmaMixture_expect_divInd_sub_common_le
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    (D : ℕ) (main error : ℝ)
    (hcell : ∀ c,
      |(law c).probability.expect
          (fun x ↦ divInd D ((law c).value x)) - main| ≤ error) :
    |(sigmaMixture weight law).probability.expect
          (fun x ↦ divInd D ((sigmaMixture weight law).value x)) - main| ≤
      error := by
  exact FiniteProbability.abs_sigmaMixture_expect_sub_common_le
    weight (fun c ↦ (law c).probability)
      (fun x ↦ divInd D ((law x.1).value x.2)) main error hcell



end PrimePowerCovariance.BoundedValuationLaw

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.FullTiltPrimePowerCovariance -/
section


/-!
# Genuine full-tilt prime-power covariance in the four-mark chamber

This module converts the actual full-tilt divisor-probability theorem into a
covariance estimate.  The product-error algebra keeps both marginal divisor
scales; it does not use the lossy bound `P(D) <= 1`.  The deterministic main
covariance is then controlled by the proved box-independent Dickman product
kernel.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FullTiltPrimePowerCovariance

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PaperScaleMarkedCell
open OmittedTiltPairChamber TwoLocalPairRestoration
open FullTiltPairChamber DickmanFourMarkProductKernel
open StructuredCellValuationLaw

noncomputable section

/-- The paper main term for `p^r q^s`, in the normalized Dickman-profile
form used by the product-kernel estimate. -/
theorem paperDivisibilityMain_pairPower_eq_profile
    {n p q r s : ℕ} (hn : 1 < n) (hp : p.Prime) (hq : q.Prime) :
    paperDivisibilityMain n (pairPower p q r s) =
      fourMarkProfile
          ((r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hylog : Real.log (y n) ≠ 0 := by
    have hypos : 0 < Real.log (y n) := by
      rw [log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (L_pos hn)
    exact hypos.ne'
  have hcast : ((pairPower p q r s : ℕ) : ℝ) =
      (p : ℝ) ^ r * (q : ℝ) ^ s := by
    simp [pairPower]
  have hlog : Real.log ((pairPower p q r s : ℕ) : ℝ) =
      (r : ℝ) * Real.log (p : ℝ) +
        (s : ℝ) * Real.log (q : ℝ) := by
    rw [hcast, Real.log_mul (pow_ne_zero r hpR) (pow_ne_zero s hqR),
      Real.log_pow, Real.log_pow]
  have hcoord : paperDivisorCoordinate n (pairPower p q r s) =
      DickmanBasic.U -
        ((r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q) := by
    unfold paperDivisorCoordinate tPrime
    rw [hlog]
    field_simp [hylog]
  unfold paperDivisibilityMain fourMarkProfile
  rw [hcoord, hcast]

















end

end Erdos390.Full.FullTiltPrimePowerCovariance

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





theorem paperDivisibilityMain_prime_eq
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime) :
    paperDivisibilityMain n p =
      DickmanBasic.F (tPrime n p) / (p : ℝ) := by
  have h := paperDivisibilityMain_pairPower_eq_profile
    (n := n) (p := p) (q := p) (r := 1) (s := 0) hn hp hp
  simpa only [pairPower, pow_one, pow_zero, mul_one,
    Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero,
    DickmanFourMarkProductKernel.fourMarkProfile_eq_F] using h





/-- Signed diagonal comparison.  The first summand is the marked
one-divisor error.  The second is the genuine Bernoulli correction together
with the diagonal kernel term inserted by the double-prime reference sum. -/
theorem abs_sigmaMixture_covII_diagonal_sub_reference_le
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hsingle : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel :
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    |mix.covII p p - squarefreeReferenceEntry n p p| ≤
      2 * E / (p : ℝ) +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel) /
          (p : ℝ) ^ 2 := by
  dsimp only
  let mix := sigmaMixture weight law
  let P : ℝ := mix.probability.expect (mix.I p)
  let Main : ℝ := paperDivisibilityMain n p
  have hpPrime := prime_of_mem_primeBand hpBand
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hprofileRaw := abs_sigmaMixture_expect_divInd_sub_common_le
    weight law p Main (E * singleWeight p 1) hsingle
  have hprofile : |P - Main| ≤ 2 * E / (p : ℝ) := by
    simpa only [P, Main, mix, BoundedValuationLaw.I] using
      (show |(sigmaMixture weight law).probability.expect
          ((sigmaMixture weight law).I p) - Main| ≤
          2 * E / (p : ℝ) by
        calc
          _ ≤ E * singleWeight p 1 := hprofileRaw
          _ = 2 * E / (p : ℝ) := by
            unfold singleWeight
            norm_num
            ring)
  have hMainEq : Main = DickmanBasic.F (tPrime n p) / (p : ℝ) :=
    paperDivisibilityMain_prime_eq hn hpPrime
  have hMainNonneg : 0 ≤ Main := by
    have hmainBound := paperDivisibilityMain_nonneg_le hn hpPrime.pos
      (by
        have hpY := le_yNat_of_mem_primeBand hpBand
        have hy : 1 ≤ yNat n := hpPrime.pos.trans_le hpY
        calc
          p ≤ yNat n := hpY
          _ ≤ yNat n ^ 4 := by nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)])
    exact hmainBound.1
  have hMainUpper : Main ≤
      (1 / DickmanBasic.rho DickmanBasic.U) / (p : ℝ) := by
    have hmainBound := paperDivisibilityMain_nonneg_le hn hpPrime.pos
      (by
        have hpY := le_yNat_of_mem_primeBand hpBand
        have hy : 1 ≤ yNat n := hpPrime.pos.trans_le hpY
        calc
          p ≤ yNat n := hpY
          _ ≤ yNat n ^ 4 := by nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)])
    change paperDivisibilityMain n p ≤ _
    convert hmainBound.2 using 1
    field_simp [DickmanBasic.rho_U_ne_zero, hpPos.ne']
  have hPNonneg : 0 ≤ P := by
    unfold P
    exact FiniteProbability.expect_nonneg mix.probability (mix.I p)
      (fun omega ↦ divInd_nonneg p (mix.value omega))
  have hPUpper : P ≤
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) / (p : ℝ) := by
    have hdiff : P - Main ≤ 2 * E / (p : ℝ) :=
      (le_abs_self (P - Main)).trans hprofile
    calc
      P ≤ Main + 2 * E / (p : ℝ) := by linarith
      _ ≤ (1 / DickmanBasic.rho DickmanBasic.U) / (p : ℝ) +
          2 * E / (p : ℝ) := add_le_add hMainUpper le_rfl
      _ = (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) / (p : ℝ) := by
        ring
  have hCoeffNonneg :
      0 ≤ 1 / DickmanBasic.rho DickmanBasic.U + 2 * E := by
    exact add_nonneg
      (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
      (mul_nonneg (by norm_num) hE)
  have hPsq : P ^ 2 ≤
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 /
        (p : ℝ) ^ 2 := by
    have hupperNonneg : 0 ≤
        (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) / (p : ℝ) :=
      div_nonneg hCoeffNonneg hpPos.le
    have hsquare := (sq_le_sq₀ hPNonneg hupperNonneg).2 hPUpper
    calc
      P ^ 2 ≤ ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) /
          (p : ℝ)) ^ 2 := hsquare
      _ = (1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 /
          (p : ℝ) ^ 2 := by ring
  have hCov : mix.covII p p = P - P ^ 2 := by
    unfold BoundedValuationLaw.covII FiniteProbability.covariance P
    have hsquare : (fun omega ↦ mix.I p omega * mix.I p omega) =
        mix.I p := by
      funext omega
      change divInd p (mix.value omega) * divInd p (mix.value omega) =
        divInd p (mix.value omega)
      nlinarith [divInd_sq p (mix.value omega)]
    rw [hsquare]
    ring
  have hKernelScaled :
      |squarefreeKernelEntry n p p| ≤ CKernel / (p : ℝ) ^ 2 := by
    unfold squarefreeKernelEntry
    have hden : 0 < (p : ℝ) * (p : ℝ) := mul_pos hpPos hpPos
    calc
      |covarianceKernel (tPrime n p) (tPrime n p) /
          ((p : ℝ) * (p : ℝ))| =
          |covarianceKernel (tPrime n p) (tPrime n p)| /
            ((p : ℝ) * (p : ℝ)) := by
        rw [abs_div, abs_of_pos hden]
      _ ≤ CKernel / ((p : ℝ) * (p : ℝ)) :=
        div_le_div_of_nonneg_right hKernel hden.le
      _ = CKernel / (p : ℝ) ^ 2 := by ring
  rw [squarefreeReferenceEntry, if_pos rfl, hCov]
  rw [← hMainEq]
  have htriangle :
      |(P - P ^ 2) - (Main + squarefreeKernelEntry n p p)| ≤
        |P - Main| + P ^ 2 + |squarefreeKernelEntry n p p| := by
    calc
      |(P - P ^ 2) - (Main + squarefreeKernelEntry n p p)| =
          |(P - Main) + (-P ^ 2 - squarefreeKernelEntry n p p)| := by
        apply congrArg abs
        ring
      _ ≤ |P - Main| + |-P ^ 2 - squarefreeKernelEntry n p p| :=
        abs_add_le _ _
      _ ≤ |P - Main| + (P ^ 2 + |squarefreeKernelEntry n p p|) := by
        gcongr
        calc
          |-P ^ 2 - squarefreeKernelEntry n p p| ≤
              |-P ^ 2| + |squarefreeKernelEntry n p p| := abs_sub _ _
          _ = P ^ 2 + |squarefreeKernelEntry n p p| := by
            rw [abs_neg, abs_of_nonneg (sq_nonneg P)]
      _ = |P - Main| + P ^ 2 + |squarefreeKernelEntry n p p| := by ring
  calc
    |(P - P ^ 2) - (Main + squarefreeKernelEntry n p p)| ≤
        |P - Main| + P ^ 2 + |squarefreeKernelEntry n p p| := htriangle
    _ ≤ 2 * E / (p : ℝ) +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 /
          (p : ℝ) ^ 2) + CKernel / (p : ℝ) ^ 2 := by
      gcongr
    _ = 2 * E / (p : ℝ) +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 + CKernel) /
          (p : ℝ) ^ 2 := by ring





end

end Erdos390.Full.SquarefreeCovarianceReference

end

universe u_1 u_2
theorem solution :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {E CKernel : Real},
  LE.le.{0} (0 : Real) E →
    ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
      (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M) {n W p : Nat},
      LT.lt.{0} (1 : Nat) n →
        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
          (∀ (c : Cell),
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.FiniteProbability.expect.{u_2}
                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c)) fun omega =>
                      Erdos390.Full.ArithmeticModel.divInd p
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                    (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
            LE.le.{0}
                (abs.{0}
                  (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel (Erdos390.Full.ArithmeticModel.tPrime n p)
                    (Erdos390.Full.ArithmeticModel.tPrime n p)))
                CKernel →
              have mix := Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} weight law;
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_1 u_2} mix p p)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry n p p)))
                (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) E) ↑p)
                  (HDiv.hDiv.{0, 0, 0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HPow.hPow.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0}
                          (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.Full.DickmanBasic.rho Erdos390.Full.DickmanBasic.U))
                          (HMul.hMul.{0, 0, 0} (2 : Real) E))
                        (2 : Nat))
                      CKernel)
                    (HPow.hPow.{0, 0, 0} ↑p (2 : Nat)))) := by
  exact @Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_diagonal_sub_reference_le
