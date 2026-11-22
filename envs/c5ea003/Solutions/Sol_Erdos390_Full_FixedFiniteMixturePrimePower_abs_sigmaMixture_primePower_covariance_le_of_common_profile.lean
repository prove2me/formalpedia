-- Prove2me | solution 1 for Erdos390.Full.FixedFiniteMixturePrimePower.abs_sigmaMixture_primePower_covariance_le_of_common_profile
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:54:44.515719+00:00
-- url     : https://prove2.me/submissions/2465158c-a2aa-4568-8562-672f493f6eec

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.DivisibilityMomentBounds -/
section


/-!
# Exact multiple-counting moment bounds

The omitted-local-score step in Lemma 7.5 expands a valuation score into
divisor indicators and then counts common multiples.  This file proves that
finite combinatorial step for an arbitrary set of positive integers bounded
by one physical endpoint.  No smooth-number estimate or probability-model
assumption enters here.
-/

open scoped BigOperators

namespace Erdos390.Full.DivisibilityMomentBounds

open ArithmeticModel

noncomputable section





/-- Products of divisor indicators combine by least common multiple. -/
theorem divInd_mul_eq_lcm (a b m : ℕ) :
    divInd a m * divInd b m = divInd (Nat.lcm a b) m := by
  by_cases ha : a ∣ m
  · by_cases hb : b ∣ m
    · have hlcm : Nat.lcm a b ∣ m := Nat.lcm_dvd ha hb
      simp [divInd, ha, hb, hlcm]
    · have hnlcm : ¬Nat.lcm a b ∣ m := by
        intro h
        exact hb ((Nat.dvd_lcm_right a b).trans h)
      simp [divInd, ha, hb, hnlcm]
  · have hnlcm : ¬Nat.lcm a b ∣ m := by
      intro h
      exact ha ((Nat.dvd_lcm_left a b).trans h)
    simp [divInd, ha, hnlcm]





























end

end Erdos390.Full.DivisibilityMomentBounds

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

/- Source module: Erdos390.Full.OmittedTiltPairChamber -/
section


/-!
# The actual omitted-tilt two-prime four-mark chamber

This file specializes the uniform marked-divisibility theorem to the literal
moduli `p^a q^b` occurring in the two-local restoration of Lemma 7.5.  All
side conditions are discharged from membership of `p,q` in the paper prime
band, the four-mark inequality `a+b <= 4`, and coprimality with the fixed
head.  In particular, the theorem below is about the genuine structured
cell and the genuine omitted valuation score, not an abstract probability
law or a conditional analytic contract.
-/

open Filter Topology

namespace Erdos390.Full.OmittedTiltPairChamber

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability ValuationScoreDomination
open PaperScaleMarkedCell OmittedTiltMarkedProbability
open TwoLocalRestoration

noncomputable section



theorem pairPower_pos {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) :
    0 < pairPower p q a b := by
  unfold pairPower
  exact Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos)











end

end Erdos390.Full.OmittedTiltPairChamber

end

/- Source module: Erdos390.Full.TwoLocalPairRestoration -/
section


/-!
# Exact max-exponent form of the two-local restoration

The numerator in the exact two-local quotient contains the product of a
forced event `p^r q^s | m` and a local-restoration event `p^a q^b | m`.
This file proves, without a squarefree shortcut, that their least common
multiple is `p^(max r a) q^(max s b)`, and rewrites the full tilted
probability in precisely the finite `N_{r,s}/N_{0,0}` form used in the
paper.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalPairRestoration

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds LocalFugacity LocalFugacityRestoration
open ValuationCutoff TwoLocalRestoration OmittedTiltPairChamber

noncomputable section

private theorem primePowerPair_coprime {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    Nat.Coprime (p ^ r) (q ^ s) := by
  have hpqCop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  exact hpqCop.pow r s

/-- The literal least common multiple of two products supported on the same
two distinct primes is obtained by taking the maximum in each exponent. -/
theorem lcm_pairPower_pairPower {p q r s a b : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    Nat.lcm (pairPower p q r s) (pairPower p q a b) =
      pairPower p q (max r a) (max s b) := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · unfold pairPower
      apply (primePowerPair_coprime hpq hp hq).mul_dvd_of_dvd_of_dvd
      · exact (Nat.pow_dvd_pow p (le_max_left r a)).trans
          (dvd_mul_right (p ^ max r a) (q ^ max s b))
      · exact (Nat.pow_dvd_pow q (le_max_left s b)).trans
          (dvd_mul_left (q ^ max s b) (p ^ max r a))
    · unfold pairPower
      apply (primePowerPair_coprime hpq hp hq).mul_dvd_of_dvd_of_dvd
      · exact (Nat.pow_dvd_pow p (le_max_right r a)).trans
          (dvd_mul_right (p ^ max r a) (q ^ max s b))
      · exact (Nat.pow_dvd_pow q (le_max_right s b)).trans
          (dvd_mul_left (q ^ max s b) (p ^ max r a))
  · unfold pairPower
    have hpMax : p ^ max r a ∣
        Nat.lcm (p ^ r * q ^ s) (p ^ a * q ^ b) := by
      rcases le_total r a with hra | har
      · rw [max_eq_right hra]
        exact (dvd_mul_right (p ^ a) (q ^ b)).trans
          (Nat.dvd_lcm_right (p ^ r * q ^ s) (p ^ a * q ^ b))
      · rw [max_eq_left har]
        exact (dvd_mul_right (p ^ r) (q ^ s)).trans
          (Nat.dvd_lcm_left (p ^ r * q ^ s) (p ^ a * q ^ b))
    have hqMax : q ^ max s b ∣
        Nat.lcm (p ^ r * q ^ s) (p ^ a * q ^ b) := by
      rcases le_total s b with hsb | hbs
      · rw [max_eq_right hsb]
        exact (dvd_mul_left (q ^ b) (p ^ a)).trans
          (Nat.dvd_lcm_right (p ^ r * q ^ s) (p ^ a * q ^ b))
      · rw [max_eq_left hbs]
        exact (dvd_mul_left (q ^ s) (p ^ r)).trans
          (Nat.dvd_lcm_left (p ^ r * q ^ s) (p ^ a * q ^ b))
    exact (primePowerPair_coprime hpq hp hq).mul_dvd_of_dvd_of_dvd
      hpMax hqMax

/-- Pointwise max-exponent identity for the actual divisor indicators. -/
theorem divInd_pairPower_mul {p q r s a b m : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    divInd (pairPower p q r s) m * divInd (pairPower p q a b) m =
      divInd (pairPower p q (max r a) (max s b)) m := by
  rw [divInd_mul_eq_lcm, lcm_pairPower_pairPower hpq hp hq]

section Cell

variable {S : Finset ℕ}



end Cell

end

end Erdos390.Full.TwoLocalPairRestoration

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







namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000



end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow

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

/-- Exact algebraic relation between a two-prime divisor covariance and the
three corresponding divisor probabilities. -/
theorem covariance_primePowers_eq_pairProbability_sub
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    mu.covariance
        (fun omega ↦ divInd (p ^ r) (value omega))
        (fun omega ↦ divInd (q ^ s) (value omega)) =
      mu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)) -
        mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
          mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) := by
  unfold FiniteProbability.covariance
  congr 2
  funext omega
  simpa only [pairPower, pow_zero, mul_one, one_mul,
    max_eq_left (Nat.zero_le _), max_eq_right (Nat.zero_le _)] using
    (divInd_pairPower_mul (m := value omega)
      (r := r) (s := 0) (a := 0) (b := s) hpq hp hq)

/-- Stable product perturbation.  The cross term `Er*Es` is retained, so
each marginal error keeps the reciprocal scale of the other prime. -/
theorem abs_primePower_covariance_sub_mainCov_le
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    {Mrs Mr Ms Ers Er Es : ℝ}
    (hEr : 0 ≤ Er)
    (hpair : |mu.expect (fun omega ↦
        divInd (pairPower p q r s) (value omega)) - Mrs| ≤ Ers)
    (hpr : |mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) - Mr| ≤ Er)
    (hqs : |mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) - Ms| ≤ Es) :
    |mu.covariance
          (fun omega ↦ divInd (p ^ r) (value omega))
          (fun omega ↦ divInd (q ^ s) (value omega)) -
        (Mrs - Mr * Ms)| ≤
      Ers + Er * |Ms| + Es * |Mr| + Er * Es := by
  let Prs := mu.expect (fun omega ↦
    divInd (pairPower p q r s) (value omega))
  let Pr := mu.expect (fun omega ↦ divInd (p ^ r) (value omega))
  let Ps := mu.expect (fun omega ↦ divInd (q ^ s) (value omega))
  have hcov := covariance_primePowers_eq_pairProbability_sub
    mu value hpq hp hq (r := r) (s := s)
  have hPs : |Ps| ≤ |Ms| + Es := by
    calc
      |Ps| = |(Ps - Ms) + Ms| := by ring_nf
      _ ≤ |Ps - Ms| + |Ms| := abs_add_le _ _
      _ ≤ Es + |Ms| := add_le_add hqs le_rfl
      _ = |Ms| + Es := by ring
  have hprod : |Pr * Ps - Mr * Ms| ≤
      Er * |Ms| + Es * |Mr| + Er * Es := by
    have hid : Pr * Ps - Mr * Ms = (Pr - Mr) * Ps + Mr * (Ps - Ms) := by
      ring
    rw [hid]
    calc
      |(Pr - Mr) * Ps + Mr * (Ps - Ms)| ≤
          |(Pr - Mr) * Ps| + |Mr * (Ps - Ms)| := abs_add_le _ _
      _ = |Pr - Mr| * |Ps| + |Mr| * |Ps - Ms| := by
        rw [abs_mul, abs_mul]
      _ ≤ Er * (|Ms| + Es) + |Mr| * Es := by
        exact add_le_add
          (mul_le_mul hpr hPs (abs_nonneg _) hEr)
          (mul_le_mul_of_nonneg_left hqs (abs_nonneg Mr))
      _ = Er * |Ms| + Es * |Mr| + Er * Es := by ring
  rw [hcov]
  change |(Prs - Pr * Ps) - (Mrs - Mr * Ms)| ≤ _
  have hid : (Prs - Pr * Ps) - (Mrs - Mr * Ms) =
      (Prs - Mrs) - (Pr * Ps - Mr * Ms) := by ring
  rw [hid]
  calc
    |(Prs - Mrs) - (Pr * Ps - Mr * Ms)| ≤
        |Prs - Mrs| + |Pr * Ps - Mr * Ms| := abs_sub _ _
    _ ≤ Ers + (Er * |Ms| + Es * |Mr| + Er * Es) :=
      add_le_add hpair hprod
    _ = Ers + Er * |Ms| + Es * |Mr| + Er * Es := by ring

/-- Exact deterministic covariance of the three paper main terms. -/
theorem paperMainCovariance_eq_profileKernel
    {n p q r s : ℕ} (hn : 1 < n) (hp : p.Prime) (hq : q.Prime) :
    paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s) =
      (fourMarkProfile
          ((r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q) -
        fourMarkProfile ((r : ℝ) * tPrime n p) *
          fourMarkProfile ((s : ℝ) * tPrime n q)) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  rw [paperDivisibilityMain_pairPower_eq_profile hn hp hq,
    paperDivisibilityMain_pairPower_eq_profile (r := r) (s := 0) hn hp hq,
    paperDivisibilityMain_pairPower_eq_profile (r := 0) (s := s) hn hp hq]
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, pow_zero, mul_one,
    one_mul]
  ring











end

end Erdos390.Full.FullTiltPrimePowerCovariance

end

/- Source module: Erdos390.Full.FullTiltPrimePowerActualChamber -/
section


/-!
# Genuine prime-power covariance on the actual four-mark chamber

The paper chamber is the arithmetic condition
`p ^ r * q ^ s <= yNat n ^ 4`, not the stronger exponent condition
`r + s <= 4`.  This distinction matters for small band primes.  This file
derives the exact logarithmic simplex inequality from the arithmetic chamber
and upgrades the full-tilt covariance theorem accordingly.
-/

namespace Erdos390.Full.FullTiltPrimePowerActualChamber

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PaperScaleMarkedCell OmittedTiltPairChamber
open FullTiltPairChamber DickmanFourMarkProductKernel
open StructuredCellValuationLaw FullTiltPrimePowerCovariance

noncomputable section

/-- Membership in the literal arithmetic four-mark chamber implies the
weighted logarithmic simplex condition used by the Dickman product kernel. -/
theorem pairPower_tPrime_sum_le_four
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W) (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4) :
    (r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q ≤ 4 := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hDR : (0 : ℝ) < (pairPower p q r s : ℕ) := by
    exact_mod_cast hDpos
  have hyNatPos : 0 < yNat n :=
    hp.pos.trans_le (le_yNat_of_mem_primeBand hpBand)
  have hyNatRpos : (0 : ℝ) < (yNat n : ℕ) := by
    exact_mod_cast hyNatPos
  have hcast : ((pairPower p q r s : ℕ) : ℝ) =
      (p : ℝ) ^ r * (q : ℝ) ^ s := by
    simp [pairPower]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hlogD : Real.log ((pairPower p q r s : ℕ) : ℝ) =
      (r : ℝ) * Real.log (p : ℝ) +
        (s : ℝ) * Real.log (q : ℝ) := by
    rw [hcast, Real.log_mul (pow_ne_zero r hpR) (pow_ne_zero s hqR),
      Real.log_pow, Real.log_pow]
  have hDCast : ((pairPower p q r s : ℕ) : ℝ) ≤
      (yNat n : ℝ) ^ 4 := by
    exact_mod_cast hD4
  have hlogDNat : Real.log ((pairPower p q r s : ℕ) : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hDR hDCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n := Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogDY :
      (r : ℝ) * Real.log (p : ℝ) +
          (s : ℝ) * Real.log (q : ℝ) ≤ 4 * Real.log (y n) := by
    rw [← hlogD]
    exact hlogDNat.trans (by linarith)
  unfold tPrime
  calc
    (r : ℝ) * (Real.log (p : ℝ) / Real.log (y n)) +
        (s : ℝ) * (Real.log (q : ℝ) / Real.log (y n)) =
      ((r : ℝ) * Real.log (p : ℝ) +
        (s : ℝ) * Real.log (q : ℝ)) / Real.log (y n) := by
          field_simp [hylog.ne']
    _ ≤ 4 := (div_le_iff₀ hylog).2 (by simpa using hlogDY)

/-- The deterministic paper covariance bound on the literal arithmetic
four-mark chamber. -/
theorem abs_paperMainCovariance_le_of_le
    {C_K : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W) (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4) :
    |paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have htp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
  have htq0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
  let x : ℝ := (r : ℝ) * tPrime n p
  let z : ℝ := (s : ℝ) * tPrime n q
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hxz4 : x + z ≤ 4 := by
    simpa only [x, z] using
      pairPower_tPrime_sum_le_four hn hpBand hqBand hD4
  rw [paperMainCovariance_eq_profileKernel hn hp hq]
  rw [abs_div]
  have hpRpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqRpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hdenpos : 0 < (p : ℝ) ^ r * (q : ℝ) ^ s :=
    mul_pos (pow_pos hpRpos r) (pow_pos hqRpos s)
  rw [abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hkernel x z hx0 hz0 hxz4) hdenpos.le





end

end Erdos390.Full.FullTiltPrimePowerActualChamber

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







theorem singleWeight_nonneg (p r : ℕ) : 0 ≤ singleWeight p r := by
  unfold singleWeight
  positivity

theorem pairWeight_eq_single_mul (p q r s : ℕ) :
    pairWeight p q r s = singleWeight p r * singleWeight q s := by
  unfold pairWeight singleWeight
  ring























/-- Algebraic closure of a joint-probability error and two marginal errors
into the covariance-error scalar used below. -/
theorem covariance_error_algebra
    {E R sp sq Ers Er Es Mr Ms : ℝ}
    (hE : 0 ≤ E) (hsp : 0 ≤ sp) (hsq : 0 ≤ sq)
    (hEs₀ : 0 ≤ Es)
    (hErs : Ers ≤ E * (sp * sq))
    (hEr : Er ≤ E * sp) (hEs : Es ≤ E * sq)
    (hMr : |Mr| ≤ R * sp) (hMs : |Ms| ≤ R * sq) :
    Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
      (E * (1 + 2 * R) + E ^ 2) * (sp * sq) := by
  have hErMs : Er * |Ms| ≤ (E * sp) * (R * sq) :=
    mul_le_mul hEr hMs (abs_nonneg Ms) (mul_nonneg hE hsp)
  have hEsMr : Es * |Mr| ≤ (E * sq) * (R * sp) :=
    mul_le_mul hEs hMr (abs_nonneg Mr) (mul_nonneg hE hsq)
  have hErEs : Er * Es ≤ (E * sp) * (E * sq) :=
    mul_le_mul hEr hEs hEs₀ (mul_nonneg hE hsp)
  calc
    Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
        E * (sp * sq) + (E * sp) * (R * sq) +
          (E * sq) * (R * sp) + (E * sp) * (E * sq) := by
      exact add_le_add (add_le_add (add_le_add hErs hErMs) hEsMr) hErEs
    _ = (E * (1 + 2 * R) + E ^ 2) * (sp * sq) := by ring

/-- The reciprocal main term is controlled by the natural one-prime weight. -/
theorem abs_paperDivisibilityMain_pow_le_singleWeight
    {n p r : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hD4 : p ^ r ≤ yNat n ^ 4) :
    |paperDivisibilityMain n (p ^ r)| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
  have hDpos : 0 < p ^ r := pow_pos hp.pos r
  have hraw := paperDivisibilityMain_nonneg_le hn hDpos hD4
  rw [abs_of_nonneg hraw.1]
  have hinv : 1 / (p : ℝ) ^ r ≤ singleWeight p r := by
    unfold singleWeight
    have hden : 0 ≤ (p : ℝ) ^ r := by positivity
    have hnum : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      nlinarith [show (0 : ℝ) ≤ r by positivity]
    exact div_le_div_of_nonneg_right hnum hden
  calc
    paperDivisibilityMain n (p ^ r) ≤
        1 / (DickmanBasic.rho DickmanBasic.U * (p ^ r : ℕ)) := hraw.2
    _ = (1 / DickmanBasic.rho DickmanBasic.U) *
        (1 / (p : ℝ) ^ r) := by
      norm_num only [Nat.cast_pow]
      ring
    _ ≤ (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r :=
      mul_le_mul_of_nonneg_left hinv
        (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)





end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.FixedFiniteMixturePrimePower -/
section


/-!
# Prime-power estimates for a fixed finite mixture

A covariance of a mixture is not the mixture of the covariances.  The
theorems in this file instead average the common one- and two-divisor
profiles first and only then form the covariance.  Consequently the
between-cell covariance is included exactly.
-/

namespace Erdos390.Full.FixedFiniteMixturePrimePower

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open FullTiltPrimePowerCovariance FullTiltPrimePowerActualChamber
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber
open PaperPrimePowerChamberError PaperPrimePowerPointwise
open PaperPrimePowerRow

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- A common marked divisibility profile gives the sharp covariance bound
for the tagged finite mixture.  In particular, no covariance is averaged
across cells. -/
theorem abs_sigmaMixture_primePower_covariance_le_of_common_profile
    {C_K E : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |DickmanFourMarkProductKernel.fourMarkProfile (x + z) -
          DickmanFourMarkProductKernel.fourMarkProfile x *
            DickmanFourMarkProductKernel.fourMarkProfile z| ≤ C_K * x * z)
    (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hprofile : ∀ c u v,
      pairPower p q u v ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q u v) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (pairPower p q u v)| ≤ E * pairWeight p q u v) :
    let mix := sigmaMixture weight law
    |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) +
        pairCovarianceScale E * pairWeight p q r s := by
  dsimp only
  let mix := sigmaMixture weight law
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hdivP : pairPower p q r 0 ∣ pairPower p q r s := by
    refine ⟨q ^ s, ?_⟩
    simp only [pairPower, pow_zero, mul_one]
  have hdivQ : pairPower p q 0 s ∣ pairPower p q r s := by
    refine ⟨p ^ r, ?_⟩
    simp only [pairPower, pow_zero, one_mul]
    exact (mul_comm (q ^ s) (p ^ r)).symm
  have hD4P : pairPower p q r 0 ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivP).trans hD4
  have hD4Q : pairPower p q 0 s ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivQ).trans hD4
  let Mrs := PaperScaleMarkedCell.paperDivisibilityMain n
    (pairPower p q r s)
  let Mr := PaperScaleMarkedCell.paperDivisibilityMain n
    (pairPower p q r 0)
  let Ms := PaperScaleMarkedCell.paperDivisibilityMain n
    (pairPower p q 0 s)
  let Ers := E * pairWeight p q r s
  let Er := E * singleWeight p r
  let Es := E * singleWeight q s
  have hpair : |mix.probability.expect
        (fun omega ↦ divInd (pairPower p q r s) (mix.value omega)) - Mrs| ≤
      Ers := by
    exact abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q r s) Mrs Ers (fun c ↦ hprofile c r s hD4)
  have hpr : |mix.probability.expect
        (fun omega ↦ divInd (p ^ r) (mix.value omega)) - Mr| ≤ Er := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q r 0) Mr (E * pairWeight p q r 0)
      (fun c ↦ hprofile c r 0 hD4P)
    simpa only [pairPower, pow_zero, mul_one, pairWeight_eq_single_mul,
      singleWeight, Nat.cast_zero, zero_add, div_one, mul_one] using hraw
  have hqs : |mix.probability.expect
        (fun omega ↦ divInd (q ^ s) (mix.value omega)) - Ms| ≤ Es := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q 0 s) Ms (E * pairWeight p q 0 s)
      (fun c ↦ hprofile c 0 s hD4Q)
    simpa only [pairPower, pow_zero, one_mul, pairWeight_eq_single_mul,
      singleWeight, Nat.cast_zero, zero_add, div_one, one_mul] using hraw
  have hEr : 0 ≤ Er := mul_nonneg hE (singleWeight_nonneg p r)
  have hprob := abs_primePower_covariance_sub_mainCov_le
    mix.probability mix.value hpq hp hq hEr
    (Mrs := Mrs) (Mr := Mr) (Ms := Ms)
    (by simpa only [mix, BoundedValuationLaw.Ip] using hpair)
    (by simpa only [mix, BoundedValuationLaw.Ip] using hpr)
    (by simpa only [mix, BoundedValuationLaw.Ip] using hqs)
  have hMr : |Mr| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
    simpa only [Mr, pairPower, pow_zero, mul_one] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp
        (by simpa only [pairPower, pow_zero, mul_one] using hD4P)
  have hMs : |Ms| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight q s := by
    simpa only [Ms, pairPower, pow_zero, one_mul] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hq
        (by simpa only [pairPower, pow_zero, one_mul] using hD4Q)
  have herr : Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
      pairCovarianceScale E * pairWeight p q r s := by
    have halg := covariance_error_algebra hE
      (singleWeight_nonneg p r) (singleWeight_nonneg q s)
      (mul_nonneg hE (singleWeight_nonneg q s))
      (show Ers ≤ E * (singleWeight p r * singleWeight q s) by
        simp only [Ers, pairWeight_eq_single_mul]
        exact le_rfl)
      (show Er ≤ E * singleWeight p r by rfl)
      (show Es ≤ E * singleWeight q s by rfl) hMr hMs
    simpa only [pairCovarianceScale, pairWeight_eq_single_mul, Ers, Er, Es]
      using halg
  have hmain := abs_paperMainCovariance_le_of_le hkernel hn hpBand hqBand hD4
  have htriangle :
      |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
        |mix.probability.covariance (mix.Ip p r) (mix.Ip q s) -
          (Mrs - Mr * Ms)| + |Mrs - Mr * Ms| := by
    have h := abs_add_le
      (mix.probability.covariance (mix.Ip p r) (mix.Ip q s) -
        (Mrs - Mr * Ms)) (Mrs - Mr * Ms)
    simpa only [sub_add_cancel] using h
  exact htriangle.trans (by
    have hsum := add_le_add (hprob.trans herr) hmain
    simpa only [Mrs, Mr, Ms, add_comm, add_left_comm, add_assoc] using hsum)





end

end Erdos390.Full.FixedFiniteMixturePrimePower

end

universe u_1 u_2
theorem solution :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {C_K E : Real},
  (∀ (x z : Real),
      LE.le.{0} (0 : Real) x →
        LE.le.{0} (0 : Real) z →
          LE.le.{0} (HAdd.hAdd.{0, 0, 0} x z) (4 : Real) →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile (HAdd.hAdd.{0, 0, 0} x z))
                  (HMul.hMul.{0, 0, 0} (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile x)
                    (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile z))))
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C_K x) z)) →
    LE.le.{0} (0 : Real) E →
      ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
        (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M)
        {n W p q r s : Nat},
        LT.lt.{0} (1 : Nat) n →
          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
            Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
              LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s)
                  (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                (∀ (c : Cell) (u v : Nat),
                    LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v)
                        (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.expect.{u_2}
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                              fun omega =>
                              Erdos390.Full.ArithmeticModel.divInd
                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                            (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                              (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v))))
                        (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q u v))) →
                  have mix := Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} weight law;
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_2}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{max u_1 u_2} mix)
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{max u_1 u_2} mix p r)
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{max u_1 u_2} mix q s)))
                    (HAdd.hAdd.{0, 0, 0}
                      (HDiv.hDiv.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} C_K
                            (HMul.hMul.{0, 0, 0} (↑r) (Erdos390.Full.ArithmeticModel.tPrime n p)))
                          (HMul.hMul.{0, 0, 0} (↑s) (Erdos390.Full.ArithmeticModel.tPrime n q)))
                        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) (HPow.hPow.{0, 0, 0} (↑q) s)))
                      (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperPrimePowerChamberError.pairCovarianceScale E)
                        (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q r s))) := by
  exact @Erdos390.Full.FixedFiniteMixturePrimePower.abs_sigmaMixture_primePower_covariance_le_of_common_profile
