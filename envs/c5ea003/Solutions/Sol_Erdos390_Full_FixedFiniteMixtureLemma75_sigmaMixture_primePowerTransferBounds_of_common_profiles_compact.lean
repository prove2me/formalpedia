-- Prove2me | solution 1 for Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:10:29.897102+00:00
-- url     : https://prove2.me/submissions/dccb87c8-7f69-4ad1-b914-f5dc97031a6b

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_FixedFiniteMixturePrimePower_abs_sigmaMixture_primePower_covariance_le_of_common_profile
import Theorems.Thm_Erdos390_Full_PaperPrimePowerGenericAggregation_primePowerTransferBounds_of_pointwise

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

/-- A common nonnegative expectation upper bound also survives convex
mixing unchanged. -/
theorem sigmaMixture_expect_le_common
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) (upper : ℝ)
    (hcell : ∀ c,
      (mu c).expect (fun x ↦ F ⟨c, x⟩) ≤ upper) :
    (sigmaMixture weight mu).expect F ≤ upper := by
  rw [sigmaMixture_expect]
  calc
    _ ≤ ∑ c, weight.mass c * upper := by
      exact Finset.sum_le_sum fun c hc ↦
        mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = upper := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

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

/-- A common reciprocal fallback estimate also survives the tagged
mixture, again at expectation level. -/
theorem sigmaMixture_expect_divInd_le_common
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    (D : ℕ) (upper : ℝ)
    (hcell : ∀ c,
      (law c).probability.expect
        (fun x ↦ divInd D ((law c).value x)) ≤ upper) :
    (sigmaMixture weight law).probability.expect
        (fun x ↦ divInd D ((sigmaMixture weight law).value x)) ≤ upper := by
  exact FiniteProbability.sigmaMixture_expect_le_common
    weight (fun c ↦ (law c).probability)
      (fun x ↦ divInd D ((law x.1).value x.2)) upper hcell

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















end

end Erdos390.Full.FullTiltPrimePowerCovariance

end

/- Source module: Erdos390.Full.FullTiltPrimePowerFallback -/
section


/-!
# Arbitrary-power fallback for the genuine full valuation tilt

The sharp Dickman estimate is used only inside the literal four-mark
chamber.  Outside it we need a box-uniform reciprocal bound.  This file
proves that bound directly on the actual structured cell, with the full
prime band present in the score, and derives the corresponding covariance
bound for two distinct primes.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPrimePowerFallback

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open ValuationScoreDomination OmittedTiltFallback
open OmittedTiltPairChamber FullTiltPairChamber
open PaperTwoLocalRestorationBound StructuredCellValuationLaw
open FullTiltPrimePowerCovariance

noncomputable section

/-- An indicator covariance is controlled by the joint event and the
product of the two marginal events. -/
theorem abs_primePower_covariance_le_joint_add_marginals
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    |mu.covariance
        (fun omega ↦ divInd (p ^ r) (value omega))
        (fun omega ↦ divInd (q ^ s) (value omega))| ≤
      mu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)) +
        mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
          mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) := by
  have hcov := covariance_primePowers_eq_pairProbability_sub
    mu value hpq hp hq (r := r) (s := s)
  rw [hcov]
  have hjoint0 : 0 ≤ mu.expect
      (fun omega ↦ divInd (pairPower p q r s) (value omega)) :=
    mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hp0 : 0 ≤ mu.expect
      (fun omega ↦ divInd (p ^ r) (value omega)) :=
    mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hq0 : 0 ≤ mu.expect
      (fun omega ↦ divInd (q ^ s) (value omega)) :=
    mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  simpa only [abs_of_nonneg hjoint0, abs_of_nonneg (mul_nonneg hp0 hq0)] using
    (abs_sub
      (mu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)))
      (mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
        mu.expect (fun omega ↦ divInd (q ^ s) (value omega))))

/-- Reciprocal event bounds imply the matching reciprocal covariance
bound.  This is the finite algebra used beyond four marks. -/
theorem abs_primePower_covariance_le_reciprocal
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ} {G : ℝ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) (hG : 0 ≤ G)
    (hjoint : mu.expect (fun omega ↦
        divInd (pairPower p q r s) (value omega)) ≤
      G / ((p : ℝ) ^ r * (q : ℝ) ^ s))
    (hpr : mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) ≤
      G / (p : ℝ) ^ r)
    (hqs : mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) ≤
      G / (q : ℝ) ^ s) :
    |mu.covariance
        (fun omega ↦ divInd (p ^ r) (value omega))
        (fun omega ↦ divInd (q ^ s) (value omega))| ≤
      (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hbase := abs_primePower_covariance_le_joint_add_marginals
    mu value hpq hp hq (r := r) (s := s)
  have hpden0 : 0 ≤ (p : ℝ) ^ r := by positivity
  have hqden0 : 0 ≤ (q : ℝ) ^ s := by positivity
  calc
    _ ≤ mu.expect (fun omega ↦
          divInd (pairPower p q r s) (value omega)) +
        mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
          mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) := hbase
    _ ≤ G / ((p : ℝ) ^ r * (q : ℝ) ^ s) +
        (G / (p : ℝ) ^ r) * (G / (q : ℝ) ^ s) := by
      apply add_le_add hjoint
      exact mul_le_mul hpr hqs
        (mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _)
        (div_nonneg hG hpden0)
    _ = (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s) := by ring





end

end Erdos390.Full.FullTiltPrimePowerFallback

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



theorem pairWeight_nonneg (p q r s : ℕ) :
    0 ≤ pairWeight p q r s := by
  unfold pairWeight
  positivity









theorem localRestorationScale_nonneg {G k : ℝ}
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ localRestorationScale G k := by
  unfold localRestorationScale
  positivity

theorem pairProbabilityScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ pairProbabilityScale epsilon G k := by
  unfold pairProbabilityScale
  have hlocal := localRestorationScale_nonneg hG hk
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem aggregateChamberScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ aggregateChamberScale epsilon G k := by
  unfold aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  exact add_nonneg (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)) hE







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

/- Source module: Erdos390.Full.PaperPrimePowerPointwise -/
section


/-!
# Literal-chamber pointwise prime-power estimates

This file performs the deterministic splice used in Lemma 7.5.  Inside the
literal arithmetic chamber `p^r q^s <= yNat n ^ 4` it uses the sharp
Dickman covariance term and the explicit restoration ledger.  Outside the
chamber it records the uniform reciprocal fallback as a named residual.
-/

namespace Erdos390.Full.PaperPrimePowerPointwise

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open OmittedTiltPairChamber
open FullTiltPairChamber FullTiltPrimePowerCovariance
open FullTiltPrimePowerActualChamber FullTiltPrimePowerFallback
open PaperPrimePowerChamberError

noncomputable section









/-- The deterministic Dickman product term is no larger than its natural
product weight. -/
theorem kernelTerm_le_pairWeight
    {C_K : ℝ} (hCK : 0 ≤ C_K) {n p q r s : ℕ}
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q) :
    C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤
      (C_K * tPrime n p * tPrime n q) * pairWeight p q r s := by
  have hrs : (r : ℝ) * (s : ℝ) ≤
      ((r : ℝ) + 1) * ((s : ℝ) + 1) := by
    nlinarith [show (0 : ℝ) ≤ r by positivity,
      show (0 : ℝ) ≤ s by positivity]
  have hcoef : 0 ≤ C_K * tPrime n p * tPrime n q := by positivity
  have hnum := mul_le_mul_of_nonneg_left hrs hcoef
  unfold pairWeight
  have hden : 0 ≤ (p : ℝ) ^ r * (q : ℝ) ^ s := by positivity
  calc
    C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) =
        (C_K * tPrime n p * tPrime n q * ((r : ℝ) * (s : ℝ))) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) := by ring
    _ ≤ (C_K * tPrime n p * tPrime n q *
          (((r : ℝ) + 1) * ((s : ℝ) + 1))) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) :=
      div_le_div_of_nonneg_right hnum hden
    _ = (C_K * tPrime n p * tPrime n q) *
        ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) := by ring

/-- Chamber/fallback splice for a genuine two-prime covariance. -/
theorem covariance_le_chamber_add_tail
    {C_K E G : ℝ} (hCK : 0 ≤ C_K) (hE : 0 ≤ E)
    {n p q r s : ℕ} {covariance chamberError : ℝ}
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hchamber : pairPower p q r s ≤ yNat n ^ 4 →
      |covariance| ≤
        C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s) + chamberError)
    (herror : pairPower p q r s ≤ yNat n ^ 4 →
      chamberError ≤ E * pairWeight p q r s)
    (hfallback : |covariance| ≤
      (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)) :
    |covariance| ≤
      (C_K * tPrime n p * tPrime n q + E) * pairWeight p q r s +
        covarianceTail G n p q r s := by
  by_cases hD4 : pairPower p q r s ≤ yNat n ^ 4
  · rw [covarianceTail, if_pos hD4, add_zero]
    calc
      |covariance| ≤
          C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
              ((p : ℝ) ^ r * (q : ℝ) ^ s) + chamberError :=
        hchamber hD4
      _ ≤ (C_K * tPrime n p * tPrime n q) * pairWeight p q r s +
          E * pairWeight p q r s :=
        add_le_add (kernelTerm_le_pairWeight hCK htp htq) (herror hD4)
      _ = (C_K * tPrime n p * tPrime n q + E) *
          pairWeight p q r s := by ring
  · rw [covarianceTail, if_neg hD4]
    exact hfallback.trans (le_add_of_nonneg_left
      (mul_nonneg (by positivity) (pairWeight_nonneg p q r s)))

/-- Chamber/fallback splice for a one-prime divisibility probability. -/
theorem probability_le_chamber_add_tail
    {R E G : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    {n p r : ℕ} {probability chamberError : ℝ}
    (hchamber : p ^ r ≤ yNat n ^ 4 →
      probability ≤ R * singleWeight p r + chamberError)
    (herror : p ^ r ≤ yNat n ^ 4 →
      chamberError ≤ E * singleWeight p r)
    (hfallback : probability ≤ G / (p : ℝ) ^ r) :
    probability ≤ (R + E) * singleWeight p r + probabilityTail G n p r := by
  by_cases hD4 : p ^ r ≤ yNat n ^ 4
  · rw [probabilityTail, if_pos hD4, add_zero]
    calc
      probability ≤ R * singleWeight p r + chamberError := hchamber hD4
      _ ≤ R * singleWeight p r + E * singleWeight p r :=
        add_le_add le_rfl (herror hD4)
      _ = (R + E) * singleWeight p r := by ring
  · rw [probabilityTail, if_neg hD4]
    exact hfallback.trans (le_add_of_nonneg_left
      (mul_nonneg (add_nonneg hR hE) (singleWeight_nonneg p r)))

end

end Erdos390.Full.PaperPrimePowerPointwise

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



/-- Chamber/fallback splice for a tagged finite mixture. -/
theorem sigmaMixture_primePower_covariance_le_chamber_add_tail
    {C_K E Gf : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |DickmanFourMarkProductKernel.fourMarkProfile (x + z) -
          DickmanFourMarkProductKernel.fourMarkProfile x *
            DickmanFourMarkProductKernel.fourMarkProfile z| ≤ C_K * x * z)
    (hCK : 0 ≤ C_K) (hE : 0 ≤ E) (hGf : 0 ≤ Gf)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hprofile : ∀ c u v,
      pairPower p q u v ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q u v) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (pairPower p q u v)| ≤ E * pairWeight p q u v)
    (hfallback : ∀ c D, 0 < D →
      (law c).probability.expect
        (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ)) :
    let mix := sigmaMixture weight law
    |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
      (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q r s + covarianceTail Gf n p q r s := by
  dsimp only
  let mix := sigmaMixture weight law
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have htp := tPrime_nonneg_of_mem_primeBand hn hpBand
  have htq := tPrime_nonneg_of_mem_primeBand hn hqBand
  apply covariance_le_chamber_add_tail hCK
    (pairCovarianceScale_nonneg hE) htp htq
  · intro hD4
    exact abs_sigmaMixture_primePower_covariance_le_of_common_profile
      hkernel hE weight law hn hpBand hqErase hD4 hprofile
  · intro hD4
    exact le_rfl
  · apply abs_primePower_covariance_le_reciprocal
      mix.probability mix.value hpq hp hq hGf
    · have h := sigmaMixture_expect_divInd_le_common weight law
        (pairPower p q r s)
        (Gf / (pairPower p q r s : ℝ))
        (fun c ↦ hfallback c (pairPower p q r s) (pairPower_pos hp hq))
      simpa only [pairPower, Nat.cast_mul, Nat.cast_pow] using h
    · have h := sigmaMixture_expect_divInd_le_common weight law (p ^ r)
        (Gf / ((p ^ r : ℕ) : ℝ))
        (fun c ↦ hfallback c (p ^ r) (Nat.pow_pos hp.pos))
      simpa only [Nat.cast_pow] using h
    · have h := sigmaMixture_expect_divInd_le_common weight law (q ^ s)
        (Gf / ((q ^ s : ℕ) : ℝ))
        (fun c ↦ hfallback c (q ^ s) (Nat.pow_pos hq.pos))
      simpa only [Nat.cast_pow] using h

/-- The matching one-prime probability splice for a tagged mixture. -/
theorem sigmaMixture_primePower_probability_le_chamber_add_tail
    {E Gf : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W p r : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W)
    (hprofile : ∀ c,
      p ^ r ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (p ^ r) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| ≤
          E * singleWeight p r)
    (hfallback : ∀ c D, 0 < D →
      (law c).probability.expect
        (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ)) :
    let mix := sigmaMixture weight law
    mix.probability.expect (mix.Ip p r) ≤
      ((1 / DickmanBasic.rho DickmanBasic.U) + E) * singleWeight p r +
        probabilityTail Gf n p r := by
  dsimp only
  let mix := sigmaMixture weight law
  have hp := prime_of_mem_primeBand hpBand
  apply probability_le_chamber_add_tail
    (chamberError := E * singleWeight p r)
    (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le) hE
  · intro hD4
    have hmix := abs_sigmaMixture_expect_divInd_sub_common_le weight law
      (p ^ r) (PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r))
      (E * singleWeight p r) (fun c ↦ hprofile c hD4)
    have hmain := abs_paperDivisibilityMain_pow_le_singleWeight hn hp hD4
    have htriangle : mix.probability.expect (mix.Ip p r) ≤
        |mix.probability.expect (mix.Ip p r) -
            PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| +
          |PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| := by
      have habs := abs_add_le
        (mix.probability.expect (mix.Ip p r) -
          PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r))
        (PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r))
      exact (le_abs_self _).trans (by simpa only [sub_add_cancel] using habs)
    have hsum := htriangle.trans (add_le_add
      (by simpa only [mix, BoundedValuationLaw.Ip] using hmix) hmain)
    simpa only [add_comm] using hsum
  · intro hD4
    exact le_rfl
  · have h := sigmaMixture_expect_divInd_le_common weight law (p ^ r)
      (Gf / ((p ^ r : ℕ) : ℝ))
      (fun c ↦ hfallback c (p ^ r) (Nat.pow_pos hp.pos))
    simpa only [mix, BoundedValuationLaw.Ip, Nat.cast_pow] using h

end

end Erdos390.Full.FixedFiniteMixturePrimePower

end

/- Source module: Erdos390.Full.PaperPrimePowerFourDisplays -/
section


/-!
# The four pointwise displays of Lemma 7.5

This file is the exact algebraic specialization of the generic actual-law
splice to `JI`, `IJ`, `JJ`, and the diagonal second-moment input.  One main
constant and one chamber remainder dominate all four orientations.
-/

namespace Erdos390.Full.PaperPrimePowerFourDisplays

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PaperPrimePowerChamberError PaperPrimePowerPointwise

noncomputable section













theorem primePowerMainConstant_nonneg {C_K : ℝ} (hCK : 0 ≤ C_K) :
    0 ≤ primePowerMainConstant C_K := by
  unfold primePowerMainConstant
  exact add_nonneg (mul_nonneg (by norm_num) hCK)
    (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)

theorem primePowerChamberRemainder_nonneg
    {epsilon G₀ k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k) :
    0 ≤ primePowerChamberRemainder epsilon G₀ k :=
  aggregateChamberScale_nonneg hepsilon hG₀ hk

/-- `JI`: the exponent-one factor is absorbed by the common factor `2`. -/
theorem ji_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p q r : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hgeneric :
      |law.probability.covariance (law.Ip p r) (law.Ip q 1)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale (pairProbabilityScale epsilon G₀ k)) *
          pairWeight p q r 1 + covarianceTail Gf n p q r 1) :
    |law.probability.covariance (law.Ip p r) (law.I q)| ≤
      (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
        (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
      eJI Gf n p q r := by
  have hIq : law.Ip q 1 = law.I q := by
    funext omega
    simp only [BoundedValuationLaw.Ip, BoundedValuationLaw.I, pow_one]
  rw [← hIq]
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) ≤
        primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith [mul_nonneg hR (mul_nonneg htp htq)]
  calc
    |law.probability.covariance (law.Ip p r) (law.Ip q 1)| ≤
        (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q r 1 + covarianceTail Gf n p q r 1 := by
      simpa only [E] using hgeneric
    _ = (2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E)) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
        eJI Gf n p q r := by
      unfold pairWeight eJI
      norm_num
      ring
    _ ≤ (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
        eJI Gf n p q r := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) le_rfl

/-- `IJ`: the transposed exponent-one specialization. -/
theorem ij_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p q s : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hgeneric :
      |law.probability.covariance (law.Ip p 1) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale (pairProbabilityScale epsilon G₀ k)) *
          pairWeight p q 1 s + covarianceTail Gf n p q 1 s) :
    |law.probability.covariance (law.I p) (law.Ip q s)| ≤
      (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
        (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
      eIJ Gf n p q s := by
  have hIp : law.Ip p 1 = law.I p := by
    funext omega
    simp only [BoundedValuationLaw.Ip, BoundedValuationLaw.I, pow_one]
  rw [← hIp]
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) ≤
        primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith [mul_nonneg hR (mul_nonneg htp htq)]
  calc
    |law.probability.covariance (law.Ip p 1) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q 1 s + covarianceTail Gf n p q 1 s := by
      simpa only [E] using hgeneric
    _ = (2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E)) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
        eIJ Gf n p q s := by
      unfold pairWeight eIJ
      norm_num
      ring
    _ ≤ (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
        eIJ Gf n p q s := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) le_rfl

/-- `JJ`: no exponent-one loss is needed. -/
theorem jj_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p q r s : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hCK : 0 ≤ C_K) (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hgeneric :
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale (pairProbabilityScale epsilon G₀ k)) *
          pairWeight p q r s + covarianceTail Gf n p q r s) :
    |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
      (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
        ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) +
      eJJ Gf n p q r s := by
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      C_K * tPrime n p * tPrime n q + pairCovarianceScale E ≤
        primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith [mul_nonneg hCK (mul_nonneg htp htq),
      mul_nonneg hR (mul_nonneg htp htq)]
  calc
    _ ≤ (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q r s + covarianceTail Gf n p q r s := by
      simpa only [E] using hgeneric
    _ ≤ (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) * pairWeight p q r s +
        covarianceTail Gf n p q r s :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef
        (pairWeight_nonneg p q r s)) le_rfl
    _ = _ := by rfl

/-- Diagonal probability display. -/
theorem diagonal_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p r : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hCK : 0 ≤ C_K) (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hgeneric : law.probability.expect (law.Ip p r) ≤
      ((1 / DickmanBasic.rho DickmanBasic.U) +
          pairProbabilityScale epsilon G₀ k) * singleWeight p r +
        probabilityTail Gf n p r) :
    law.probability.expect (law.Ip p r) ≤
      (primePowerMainConstant C_K +
          primePowerChamberRemainder epsilon G₀ k) *
        (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD Gf n p r := by
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      (1 / DickmanBasic.rho DickmanBasic.U) + E ≤
        primePowerMainConstant C_K +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith
  calc
    law.probability.expect (law.Ip p r) ≤
        ((1 / DickmanBasic.rho DickmanBasic.U) + E) * singleWeight p r +
          probabilityTail Gf n p r := by simpa only [E] using hgeneric
    _ ≤ (primePowerMainConstant C_K +
          primePowerChamberRemainder epsilon G₀ k) * singleWeight p r +
        probabilityTail Gf n p r :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (singleWeight_nonneg p r))
        le_rfl
    _ = _ := by rfl

end

end Erdos390.Full.PaperPrimePowerFourDisplays

end

/- Source module: Erdos390.Full.FixedFiniteMixtureLemma75 -/
section


/-!
# Lemma 7.5 for a fixed finite mixture

The hypotheses are common one- and two-divisor profiles on every component
cell, together with the common reciprocal fallback and the deterministic
tail ledgers.  The conclusion is the exact five-field statement used in
the paper.  The mixture weights are arbitrary; the proof includes the
between-cell covariance through the expectation-level mixture theorems.
-/

open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureLemma75

open ArithmeticModel Scale FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber DickmanFourMarkProductKernel
open PaperPrimePowerChamberError PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerRow
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixturePrimePower PaperValuationCutoff ValuationCutoff

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- Exact finite-`n` fixed-mixture form of paper Lemma 7.5. -/
theorem sigmaMixture_primePowerTransferBounds_of_common_profiles
    {C_K epsilon G₀ k Gf Tlin Tquad Tdiag Trow : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) - fourMarkProfile x * fourMarkProfile z| ≤
        C_K * x * z)
    (hCK : 0 ≤ C_K) (hε : 0 ≤ epsilon) (hG₀ : 0 ≤ G₀)
    (hk : 0 ≤ k) (hGf : 0 ≤ Gf)
    (hTlin : 0 ≤ Tlin) (hTquad : 0 ≤ Tquad)
    (hTdiag : 0 ≤ Tdiag) (hTrow : 0 ≤ Trow)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n) (hW : 1 < W)
    (hpairProfile : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
      pairPower p q r s ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q r s) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (pairPower p q r s)| ≤
        pairProbabilityScale epsilon G₀ k * pairWeight p q r s)
    (hsingleProfile : ∀ c p, p ∈ primeBand n W → ∀ r,
      p ^ r ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (p ^ r) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| ≤
        pairProbabilityScale epsilon G₀ k * singleWeight p r)
    (hfallback : ∀ c D, 0 < D →
      (law c).probability.expect
        (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ))
    (htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M), eJI Gf n p q r) ≤
        Tlin * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)))
    (htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (valuationCutoff q M), eIJ Gf n p q s) ≤
        Tlin * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2)
    (htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        ∑ s ∈ highExponents (valuationCutoff q M), eJJ Gf n p q r s) ≤
          Tquad * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2)
    (htailD : ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r)) ≤
          Tdiag * (1 / (p : ℝ)) ^ 2)
    (htailRow : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            (((∑ r ∈ highExponents (valuationCutoff p M),
                eJI Gf n p q r)) +
              (∑ s ∈ highExponents (valuationCutoff q M),
                eIJ Gf n p q s) +
              (∑ r ∈ highExponents (valuationCutoff p M),
                ∑ s ∈ highExponents (valuationCutoff q M),
                  eJJ Gf n p q r s))) +
          3 * (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r))) ≤ Trow)
    (hbandT : PrimeSums.bandTReciprocalSum n W ≤ 2 * Real.log 4) :
    PrimePowerTransferBounds (sigmaMixture weight law) n W
      (paperPrimePowerConstant C_K)
      (genericAggregationRemainder
        (primePowerChamberRemainder epsilon G₀ k)
        Tlin Tquad Tdiag Trow n W) := by
  let mix := sigmaMixture weight law
  let Eprob := pairProbabilityScale epsilon G₀ k
  let Ecov := pairCovarianceScale Eprob
  let Eagg := primePowerChamberRemainder epsilon G₀ k
  have hEprob : 0 ≤ Eprob := pairProbabilityScale_nonneg hε hG₀ hk
  have hEagg : 0 ≤ Eagg := primePowerChamberRemainder_nonneg hε hG₀ hk
  have hgeneric : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p, ∀ r s : ℕ,
      |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q + Ecov) * pairWeight p q r s +
          covarianceTail Gf n p q r s := by
    intro p hpBand q hqErase r s
    exact sigmaMixture_primePower_covariance_le_chamber_add_tail
      hkernel hCK hEprob hGf weight law hn hpBand hqErase
      (fun c u v hD4 ↦ hpairProfile c p hpBand q hqErase u v hD4)
      hfallback
  have hdiag : ∀ p ∈ primeBand n W, ∀ r : ℕ,
      mix.probability.expect (mix.Ip p r) ≤
        ((1 / DickmanBasic.rho DickmanBasic.U) + Eprob) *
            singleWeight p r + probabilityTail Gf n p r := by
    intro p hpBand r
    exact sigmaMixture_primePower_probability_le_chamber_add_tail
      hEprob weight law hn hpBand
        (fun c hD4 ↦ hsingleProfile c p hpBand r hD4) hfallback
  have hCmain : 0 ≤ primePowerMainConstant C_K :=
    primePowerMainConstant_nonneg hCK
  have hJIpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      |mix.probability.covariance (mix.Ip p r) (mix.I q)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q + Eagg) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
            eJI Gf n p q r := by
    intro p hpBand q hqErase r hr
    exact ji_display_of_generic mix hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (by simpa only [Eprob, Ecov, Eagg] using
        hgeneric p hpBand q hqErase r 1)
  have hIJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q M),
      |mix.probability.covariance (mix.I p) (mix.Ip q s)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q + Eagg) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
            eIJ Gf n p q s := by
    intro p hpBand q hqErase s hs
    exact ij_display_of_generic mix hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (by simpa only [Eprob, Ecov, Eagg] using
        hgeneric p hpBand q hqErase 1 s)
  have hJJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q + Eagg) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) + eJJ Gf n p q r s := by
    intro p hpBand q hqErase r hr s hs
    exact jj_display_of_generic mix hCK hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (by simpa only [Eprob, Ecov, Eagg] using
        hgeneric p hpBand q hqErase r s)
  have hDpoint : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p M),
      mix.probability.expect (mix.Ip p r) ≤
        (primePowerMainConstant C_K + Eagg) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD Gf n p r := by
    intro p hpBand r hr
    exact diagonal_display_of_generic mix hCK hε hG₀ hk
      (by simpa only [Eprob, Eagg] using hdiag p hpBand r)
  have hfinal := primePowerTransferBounds_of_pointwise mix hn hW
    hCmain hEagg hTlin hTquad hTdiag hTrow
    hJIpoint hIJpoint hJJpoint hDpoint htailJI htailIJ htailJJ htailD
    htailRow hbandT
  simpa only [paperPrimePowerConstant, mix] using hfinal

end

end Erdos390.Full.FixedFiniteMixtureLemma75

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal001_002.{u_1, u_2} := by
  exact @Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles
