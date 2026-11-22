-- Prove2me | solution 1 for Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:31:14.125547+00:00
-- url     : https://prove2.me/submissions/99980f2a-61b4-41e5-97ab-7168634874da

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







/-- The three common marked profiles imply a signed covariance comparison
for two distinct moving primes.  The error is still at product-reciprocal
scale. -/
theorem abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
    {E : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hpairProfile : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hpProfile : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hqProfile : ∀ c,
      |(law c).probability.expect
          (fun omega ↦ divInd q ((law c).value omega)) -
        paperDivisibilityMain n q| ≤ E * singleWeight q 1) :
    let mix := sigmaMixture weight law
    |mix.covII p q - squarefreeKernelEntry n p q| ≤
      pairCovarianceScale E * pairWeight p q 1 1 := by
  dsimp only
  let mix := sigmaMixture weight law
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hpPos : 0 < p := hp.pos
  have hqPos : 0 < q := hq.pos
  have hD4 : pairPower p q 1 1 ≤ yNat n ^ 4 := by
    have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
    have hqY : q ≤ yNat n := le_yNat_of_mem_primeBand hqBand
    unfold pairPower
    simp only [pow_one]
    calc
      p * q ≤ yNat n * yNat n := Nat.mul_le_mul hpY hqY
      _ ≤ yNat n ^ 4 := by
        have hy : 1 ≤ yNat n := hpPos.trans_le hpY
        nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)]
  have hD4P : pairPower p q 1 0 ≤ yNat n ^ 4 := by
    have hdiv : pairPower p q 1 0 ∣ pairPower p q 1 1 := by
      refine ⟨q, ?_⟩
      simp [pairPower]
    exact (Nat.le_of_dvd (pairPower_pos hp hq) hdiv).trans hD4
  have hD4Q : pairPower p q 0 1 ≤ yNat n ^ 4 := by
    have hdiv : pairPower p q 0 1 ∣ pairPower p q 1 1 := by
      refine ⟨p, ?_⟩
      simp [pairPower, Nat.mul_comm]
    exact (Nat.le_of_dvd (pairPower_pos hp hq) hdiv).trans hD4
  let Mrs := paperDivisibilityMain n (pairPower p q 1 1)
  let Mr := paperDivisibilityMain n (pairPower p q 1 0)
  let Ms := paperDivisibilityMain n (pairPower p q 0 1)
  let Ers := E * pairWeight p q 1 1
  let Er := E * singleWeight p 1
  let Es := E * singleWeight q 1
  have hpair : |mix.probability.expect
        (fun omega ↦ divInd (pairPower p q 1 1) (mix.value omega)) - Mrs| ≤
      Ers := by
    exact abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (pairPower p q 1 1) Mrs Ers hpairProfile
  have hpr : |mix.probability.expect
        (fun omega ↦ divInd (p ^ 1) (mix.value omega)) - Mr| ≤ Er := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      p (paperDivisibilityMain n p) (E * singleWeight p 1) hpProfile
    simpa only [Er, Mr, pairPower, pow_zero, pow_one, mul_one] using hraw
  have hqs : |mix.probability.expect
        (fun omega ↦ divInd (q ^ 1) (mix.value omega)) - Ms| ≤ Es := by
    have hraw := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      q (paperDivisibilityMain n q) (E * singleWeight q 1) hqProfile
    simpa only [Es, Ms, pairPower, pow_zero, pow_one, one_mul] using hraw
  have hEr : 0 ≤ Er := mul_nonneg hE (singleWeight_nonneg p 1)
  have hprob := abs_primePower_covariance_sub_mainCov_le
    mix.probability mix.value hpq hp hq hEr hpair hpr hqs
  have hMr : |Mr| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p 1 := by
    simpa only [Mr, pairPower, pow_zero, mul_one] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp
        (by simpa only [pairPower, pow_zero, mul_one] using hD4P)
  have hMs : |Ms| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight q 1 := by
    simpa only [Ms, pairPower, pow_zero, one_mul] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hq
        (by simpa only [pairPower, pow_zero, one_mul] using hD4Q)
  have herr : Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
      pairCovarianceScale E * pairWeight p q 1 1 := by
    have halg := covariance_error_algebra hE
      (singleWeight_nonneg p 1) (singleWeight_nonneg q 1)
      (mul_nonneg hE (singleWeight_nonneg q 1))
      (show Ers ≤ E * (singleWeight p 1 * singleWeight q 1) by
        rw [show Ers = E * pairWeight p q 1 1 by rfl,
          pairWeight_eq_single_mul])
      (show Er ≤ E * singleWeight p 1 by rfl)
      (show Es ≤ E * singleWeight q 1 by rfl) hMr hMs
    simpa only [pairCovarianceScale, pairWeight_eq_single_mul, Ers, Er, Es]
      using halg
  have hmain := paperMainCovariance_eq_profileKernel
    (r := 1) (s := 1) hn hp hq
  have hmain' : Mrs - Mr * Ms = squarefreeKernelEntry n p q := by
    rw [hmain]
    unfold squarefreeKernelEntry covarianceKernel
    simp only [Nat.cast_one, one_mul, pow_one,
      DickmanFourMarkProductKernel.fourMarkProfile_eq_F]
  change |mix.probability.covariance (mix.I p) (mix.I q) -
      squarefreeKernelEntry n p q| ≤ _
  have hprob' :
      |mix.probability.covariance (mix.I p) (mix.I q) - (Mrs - Mr * Ms)| ≤
        Ers + Er * |Ms| + Es * |Mr| + Er * Es := by
    simpa only [BoundedValuationLaw.Ip, pow_one] using hprob
  rw [hmain'] at hprob'
  exact hprob'.trans herr









end

end Erdos390.Full.SquarefreeCovarianceReference

end

universe u_1 u_2
theorem solution :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {E : Real},
  LE.le.{0} (0 : Real) E →
    ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
      (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M) {n W p q : Nat},
      LT.lt.{0} (1 : Nat) n →
        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
          Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
            (∀ (c : Cell),
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.FiniteProbability.expect.{u_2}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c)) fun omega =>
                        Erdos390.Full.ArithmeticModel.divInd
                          (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat))
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                        (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                  (HMul.hMul.{0, 0, 0} E
                    (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat)))) →
              (∀ (c : Cell),
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.FiniteProbability.expect.{u_2}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                          fun omega =>
                          Erdos390.Full.ArithmeticModel.divInd p
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                    (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
                (∀ (c : Cell),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.expect.{u_2}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                            fun omega =>
                            Erdos390.Full.ArithmeticModel.divInd q
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n q)))
                      (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight q (1 : Nat)))) →
                  have mix := Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} weight law;
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_1 u_2} mix p q)
                        (Erdos390.Full.SquarefreeCovarianceReference.squarefreeKernelEntry n p q)))
                    (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperPrimePowerChamberError.pairCovarianceScale E)
                      (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))) := by
  exact @Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
