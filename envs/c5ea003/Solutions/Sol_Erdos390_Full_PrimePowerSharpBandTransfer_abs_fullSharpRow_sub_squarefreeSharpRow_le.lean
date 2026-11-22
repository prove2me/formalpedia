-- Prove2me | solution 1 for Erdos390.Full.PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:26:26.884611+00:00
-- url     : https://prove2.me/submissions/ca0af9e0-fbd1-498e-8067-288f645acc72

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
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

theorem divInd_le_one (d m : ℕ) : divInd d m ≤ 1 := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]





















/-- A prime valuation is the finite sum of its positive-power divisibility
indicators.  The common exponent cutoff may be any `M` above the sampled
integer, hence in particular a fixed physical upper bound for a whole cell. -/
theorem valuation_eq_sum_divInd_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuation p m = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  have hMpow : m ≤ p ^ M := by
    exact hmM.trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
  have hfilter := Nat.Ico_filter_pow_dvd_eq hp hm.ne' hMpow
  have hcard := Nat.factorization_eq_card_pow_dvd m hp
  calc
    valuation p m = (m.factorization p : ℝ) := rfl
    _ = (((Finset.Ico 1 m).filter fun k => p ^ k ∣ m).card : ℝ) := by
      exact_mod_cast hcard
    _ = (((Finset.Icc 1 M).filter fun k => p ^ k ∣ m).card : ℝ) := by
      rw [hfilter]
    _ = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
      simp [positiveExponents, divInd]





private theorem positiveExponents_eq_insert_high {M : ℕ} (hM : 1 ≤ M) :
    positiveExponents M = insert 1 (highExponents M) := by
  ext k
  simp only [mem_positiveExponents, Finset.mem_insert, mem_highExponents]
  omega

/-- The paper's identity `J_p = sum_{k≥2} 1_{p^k ∣ m}`, with a
common finite cutoff valid throughout a physical cell. -/
theorem higherValuation_eq_sum_high_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m = ∑ k ∈ highExponents M, divInd (p ^ k) m := by
  have hM : 1 ≤ M := hm.trans_le hmM
  rw [higherValuation, valuation_eq_sum_divInd_of_le hp hm hmM,
    positiveExponents_eq_insert_high hM]
  have h1not : 1 ∉ highExponents M := by simp
  rw [Finset.sum_insert h1not]
  simp [divInd]

theorem higherValuation_eq_sum_high {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ∑ k ∈ highExponents m, divInd (p ^ k) m :=
  higherValuation_eq_sum_high_of_le hp hm le_rfl











theorem higherValuation_nonneg {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    0 ≤ higherValuation p m := by
  rw [higherValuation_eq_sum_high hp hm]
  exact Finset.sum_nonneg fun k hk => divInd_nonneg (p ^ k) m

private theorem natCast_le_square (a : ℕ) : (a : ℝ) ≤ (a : ℝ) ^ 2 := by
  cases a with
  | zero => norm_num
  | succ a =>
      have h : (1 : ℝ) ≤ (a.succ : ℝ) := by exact_mod_cast a.succ_pos
      nlinarith

private theorem higherValuation_eq_natCast_pred {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ((m.factorization p - 1 : ℕ) : ℝ) := by
  by_cases hdvd : p ∣ m
  · have hfac : 1 ≤ m.factorization p :=
      (hp.dvd_iff_one_le_factorization hm.ne').mp hdvd
    rw [higherValuation, valuation, divInd]
    simp only [if_pos hdvd]
    rw [Nat.cast_sub hfac]
    norm_num
  · have hfac : m.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hdvd
    simp [higherValuation, valuation, divInd, hdvd, hfac]

/-- Since `J_p` is a nonnegative integer, `J_p ≤ J_p²`. -/
theorem higherValuation_le_sq {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m ≤ higherValuation p m ^ 2 := by
  rw [higherValuation_eq_natCast_pred hp hm]
  exact natCast_le_square _



end Erdos390.Full.ArithmeticModel

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









theorem expect_mono (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (hFG : ∀ omega, F omega ≤ G omega) : mu.expect F ≤ mu.expect G := by
  unfold expect
  apply Finset.sum_le_sum
  intro omega _
  exact mul_le_mul_of_nonneg_left (hFG omega) (mu.mass_nonneg omega)

theorem covariance_self_nonneg (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    0 ≤ mu.covariance F F := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (F omega * F omega)) =
      ∑ omega, mu.mass omega * F omega ^ 2 by
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * F omega) *
      (∑ omega, mu.mass omega * F omega) =
        (∑ omega, mu.mass omega * F omega) ^ 2 by ring]
  rw [PatternMixture.weightedVariance_pairDifference mu.mass F mu.mass_sum]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (mul_nonneg (mu.mass_nonneg i) (mu.mass_nonneg j)) (sq_nonneg _)

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



















theorem V_eq_I_add_J (law : BoundedValuationLaw Omega M) (p : ℕ) :
    law.V p = fun omega ↦ law.I p omega + law.J p omega := by
  funext omega
  simp only [V, I, J, higherValuation]
  ring



/-- Exact decomposition of the full-valuation covariance error. -/
theorem covVV_sub_covII (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    law.covVV p q - law.covII p q =
      law.covJI p q + law.covIJ p q + law.covJJ p q := by
  rw [covVV, covII, covJI, covIJ, covJJ,
    law.V_eq_I_add_J p, law.V_eq_I_add_J q]
  rw [law.probability.covariance_add_left,
    law.probability.covariance_add_right,
    law.probability.covariance_add_right]
  ring

theorem abs_covVV_sub_covII_le (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    |law.covVV p q - law.covII p q| ≤
      |law.covJI p q| + |law.covIJ p q| + |law.covJJ p q| := by
  rw [law.covVV_sub_covII p q]
  exact (abs_add_three _ _ _)







theorem I_nonneg (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    0 ≤ law.I p omega := divInd_nonneg _ _

theorem I_le_one (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    law.I p omega ≤ 1 := divInd_le_one _ _

theorem J_nonneg (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    0 ≤ law.J p omega := higherValuation_nonneg hp (law.value_pos omega)

theorem J_le_sq (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    law.J p omega ≤ law.J p omega ^ 2 :=
  higherValuation_le_sq hp (law.value_pos omega)

theorem I_mul_J (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    law.I p omega * law.J p omega = law.J p omega := by
  exact divInd_mul_higherValuation p (law.value omega)

/-- On the diagonal, the paper's bound
`|Var(V_p)-Var(I_p)| ≤ 3 E[J_p²]` follows from the actual integer-valued
columns, not from a stylized random-variable identity. -/
theorem abs_covVV_sub_covII_diagonal_le
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    |law.covVV p p - law.covII p p| ≤
      3 * law.probability.expect (fun omega ↦ law.J p omega ^ 2) := by
  let EI := law.probability.expect (law.I p)
  let EJ := law.probability.expect (law.J p)
  let EJ2 := law.probability.expect (fun omega ↦ law.J p omega ^ 2)
  have hEI0 : 0 ≤ EI := law.probability.expect_nonneg _ (law.I_nonneg p)
  have hEI1 : EI ≤ 1 := by
    calc
      EI ≤ law.probability.expect (fun _ ↦ 1) :=
        law.probability.expect_mono _ _ (law.I_le_one p)
      _ = 1 := by simp [FiniteProbability.expect, law.probability.mass_sum]
  have hEJ0 : 0 ≤ EJ :=
    law.probability.expect_nonneg _ (law.J_nonneg hp)
  have hEJ2_0 : 0 ≤ EJ2 :=
    law.probability.expect_nonneg _ fun omega ↦ sq_nonneg _
  have hEJle : EJ ≤ EJ2 :=
    law.probability.expect_mono _ _ (law.J_le_sq hp)
  have hprod : law.probability.expect
      (fun omega ↦ law.I p omega * law.J p omega) = EJ := by
    change law.probability.expect
      (fun omega ↦ law.I p omega * law.J p omega) =
        law.probability.expect (law.J p)
    congr 1
    funext omega
    exact law.I_mul_J p omega
  have hcovIJ : law.covIJ p p = (1 - EI) * EJ := by
    unfold covIJ FiniteProbability.covariance
    rw [hprod]
    ring
  have hcovIJ0 : 0 ≤ law.covIJ p p := by
    rw [hcovIJ]
    exact mul_nonneg (sub_nonneg.mpr hEI1) hEJ0
  have hcovIJle : law.covIJ p p ≤ EJ2 := by
    rw [hcovIJ]
    have hfactor : (1 - EI) * EJ ≤ EJ := by
      nlinarith [mul_nonneg hEI0 hEJ0]
    exact hfactor.trans hEJle
  have hcovJI : law.covJI p p = law.covIJ p p := by
    unfold covJI covIJ
    exact law.probability.covariance_comm _ _
  have hvarJ0 : 0 ≤ law.covJJ p p := by
    exact law.probability.covariance_self_nonneg (law.J p)
  have hvarJle : law.covJJ p p ≤ EJ2 := by
    unfold covJJ FiniteProbability.covariance
    change law.probability.expect (fun omega ↦ law.J p omega * law.J p omega) -
        EJ * EJ ≤ EJ2
    have hfirst : law.probability.expect
        (fun omega ↦ law.J p omega * law.J p omega) = EJ2 := by
      congr 1
      funext omega
      ring
    rw [hfirst]
    nlinarith [sq_nonneg EJ]
  rw [law.covVV_sub_covII p p, hcovJI]
  rw [abs_of_nonneg (by linarith)]
  linarith

end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.ValuationCutoff -/
section


/-!
# The actual logarithmic valuation cutoff

The local fugacity expansion must be truncated at
`floor(log M / log p)`, not at the much larger physical endpoint `M`.
This module identifies Mathlib's `Nat.log p M` as a valid common cutoff for
all positive integers `m ≤ M`, proves the exact restored factor at that
cutoff, and compares it with the real logarithmic ratio used in the paper.
-/

namespace Erdos390.Full.ValuationCutoff

open ArithmeticModel LocalFugacityRestoration

noncomputable section



/-- Every actual `p`-adic valuation in `(0,M]` is below the logarithmic
cutoff. -/
theorem factorization_le_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    m.factorization p ≤ valuationCutoff p M := by
  have hdvd : p ^ m.factorization p ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm.ne').2 le_rfl
  have hpowm : p ^ m.factorization p ≤ m := Nat.le_of_dvd hm hdvd
  exact Nat.le_log_of_pow_le hp.one_lt (hpowm.trans hmM)









end

end Erdos390.Full.ValuationCutoff

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













end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PrimePowerCutoffCovariance -/
section


/-!
# Exact logarithmic cutoffs in the prime-power covariance expansion

`PrimePowerCovariance` expands the higher-valuation column using the common
physical endpoint.  The paper's local-factor analysis instead uses the exact
logarithmic cutoff `valuationCutoff p M`.  This file proves that the two finite
sums agree for every value in `(0,M]`, and consequently rewrites every actual
`JI`, `IJ`, `JJ`, and diagonal-moment expression at that logarithmic cutoff.

There is no asymptotic or probabilistic input here: the truncation follows
from the literal inequality

`factorization p m <= valuationCutoff p M`.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerCutoffCovariance

open ArithmeticModel PowerLedger ValuationCutoff
open FiniteProbability PrimePowerCovariance

noncomputable section

private theorem sum_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A, divInd (p ^ k) m) =
      ∑ k ∈ highExponents B, divInd (p ^ k) m := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega



/-- Exact higher-valuation expansion at the logarithmic cutoff. -/
theorem higherValuation_eq_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m =
      ∑ k ∈ highExponents (valuationCutoff p M), divInd (p ^ k) m := by
  rw [higherValuation_eq_sum_high_of_le hp hm hmM]
  exact sum_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)



namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]



end FiniteProbability

variable {Omega : Type*} [Fintype Omega] {M : ℕ}

/-- The actual `J_p` column, cut off at `floor(log_p M)`. -/
theorem J_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.J p = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M), law.Ip p k omega := by
  funext omega
  exact higherValuation_eq_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

/-- `JI` as the literal finite sum at the exact logarithmic cutoff. -/
theorem covJI_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) (q : ℕ) :
    law.covJI p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.covariance (law.Ip p k) (law.I q) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJI,
    J_eq_valuationCutoff_sum law hp,
    law.probability.covariance_sum_left]

/-- `IJ` as the transposed finite sum at the exact logarithmic cutoff. -/
theorem covIJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) (p : ℕ) {q : ℕ} (hq : q.Prime) :
    law.covIJ p q =
      ∑ k ∈ highExponents (valuationCutoff q M),
        law.probability.covariance (law.I p) (law.Ip q k) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covIJ,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_right]

/-- `JJ` as the literal double sum at the two exact logarithmic cutoffs. -/
theorem covJJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    law.covJJ p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          law.probability.covariance (law.Ip p k) (law.Ip q l) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJJ,
    J_eq_valuationCutoff_sum law hp,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.covariance_sum_right]





end

end Erdos390.Full.PrimePowerCutoffCovariance

end

/- Source module: Erdos390.Full.PrimePowerSharpBandTransfer -/
section


/-!
# Prime-power transfer in the moving-low sharp band norm

The already-proved row field of `PrimePowerTransferBounds` is sufficient for
fixed positive bands, but dividing that collapsed row bound by the moving low
centre would incorrectly charge the box-independent `C_pow / W` term by
`1 / alpha_0`.  This file retains the first four fields of the certificate
until after band averaging.  The factors `t_p t_q` then cancel the output
centre exactly; only the genuine analytic remainder is divided by that
centre.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerSharpBandTransfer

set_option maxHeartbeats 2400000

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRow
open PrimePowerCutoffCovariance
open SquarefreeSharpBandTransfer

noncomputable section

variable {Omega Band : Type*} [Fintype Omega]
  [Fintype Band] [DecidableEq Band]
  {M n W : ℕ}





/-- The three off-diagonal prime-power displays imply the corresponding
entrywise full-versus-squarefree covariance estimate. -/
theorem abs_covVV_sub_covII_le_of_transferBounds_of_ne
    (law : BoundedValuationLaw Omega M)
    {Cpow epsilon : ℝ}
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    (p q : BandPrime n W) (hpq : p ≠ q) :
    |law.covVV p.1 q.1 - law.covII p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
          (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
          (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
          (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
  have hqErase : q.1 ∈ (primeBand n W).erase p.1 :=
    Finset.mem_erase.mpr ⟨fun h ↦ hpq (Subtype.ext h.symm), q.2⟩
  have hji : |law.covJI p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) := by
    rw [covJI_eq_valuationCutoff_sum law (prime_of_mem_primeBand p.2)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (h75.ji p.1 p.2 q.1 hqErase)
  have hij : |law.covIJ p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 := by
    rw [covIJ_eq_valuationCutoff_sum law p.1
      (prime_of_mem_primeBand q.2)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (h75.ij p.1 p.2 q.1 hqErase)
  have hjj : |law.covJJ p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
    rw [covJJ_eq_valuationCutoff_sum law (prime_of_mem_primeBand p.2)
      (prime_of_mem_primeBand q.2)]
    calc
      |∑ r ∈ highExponents (ValuationCutoff.valuationCutoff p.1 M),
          ∑ s ∈ highExponents (ValuationCutoff.valuationCutoff q.1 M),
          law.probability.covariance (law.Ip p.1 r) (law.Ip q.1 s)| ≤
          ∑ r ∈ highExponents (ValuationCutoff.valuationCutoff p.1 M),
            |∑ s ∈ highExponents (ValuationCutoff.valuationCutoff q.1 M),
              law.probability.covariance (law.Ip p.1 r)
                (law.Ip q.1 s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ highExponents (ValuationCutoff.valuationCutoff p.1 M),
          ∑ s ∈ highExponents (ValuationCutoff.valuationCutoff q.1 M),
          |law.probability.covariance (law.Ip p.1 r)
            (law.Ip q.1 s)| := by
        apply Finset.sum_le_sum
        intro r hr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := h75.jj p.1 p.2 q.1 hqErase
  exact (law.abs_covVV_sub_covII_le p.1 q.1).trans (by linarith)

/-- Diagonal specialization of the fourth transfer display. -/
theorem abs_covVV_sub_covII_le_of_transferBounds_diagonal
    (law : BoundedValuationLaw Omega M)
    {Cpow epsilon : ℝ}
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    (p : BandPrime n W) :
    |law.covVV p.1 p.1 - law.covII p.1 p.1| ≤
      3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 := by
  exact (law.abs_covVV_sub_covII_diagonal_le
      (prime_of_mem_primeBand p.2)).trans (by
    have h := h75.diagonal p.1 p.2
    nlinarith)

/-- The five displays of Lemma 7.5 aggregated in the genuine moving-low
sharp norm.  The box-independent term is *not* divided by the low centre;
only `epsilon / center i` remains. -/
theorem abs_fullSharpRow_sub_squarefreeSharpRow_le
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (hn : 1 < n) (hW : 1 < W)
    {Cpow epsilon : ℝ} (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |fullSharpRow law P q i - squarefreeSharpRow law P q i| ≤
      3 * Cpow * (bandTReciprocalSum n W + 1) * (1 / (W : ℝ)) +
        3 * epsilon *
          (bandTReciprocalSum n W / P.center i + 1) *
            (1 / (W : ℝ)) := by
  let T := bandTReciprocalSum n W
  have hmass : 0 < P.mass i := P.data.mass_pos i
  have hcenter : 0 < P.center i := P.center_pos hn i
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.zero_lt_of_lt hW
  have hWinvNonneg : 0 ≤ (1 / (W : ℝ)) := by positivity
  have hWinvOne : (1 / (W : ℝ)) ≤ 1 := by
    have hWone : (1 : ℝ) ≤ W := by exact_mod_cast hW.le
    simpa only [one_div_one] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 1) hWone
  have hT : 0 ≤ T := by
    dsimp only [T]
    unfold bandTReciprocalSum
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (tPrime_nonneg_of_mem_primeBand hn hp)
      (by positivity)
  have hprimePos (p : BandPrime n W) : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hprimeInvNonneg (p : BandPrime n W) :
      0 ≤ (1 / (p.1 : ℝ)) := by positivity
  have hprimeInvW (p : BandPrime n W) :
      (1 / (p.1 : ℝ)) ≤ 1 / (W : ℝ) := by
    exact one_div_le_one_div_of_le hWpos
      (by exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le)
  have htNonneg (p : BandPrime n W) : 0 ≤ tPrime n p.1 :=
    tPrime_nonneg_of_mem_primeBand hn p.2
  have htOne (p : BandPrime n W) : tPrime n p.1 ≤ 1 :=
    tPrime_le_one_of_mem_primeBand hn p.2
  have hcenterNonneg (j : Band) : 0 ≤ P.center j :=
    (P.center_pos hn j).le
  have hcenterOne (j : Band) : P.center j ≤ 1 :=
    (P.center_mem_zero_one hn j).2
  have hcoeff (j : Band) : |P.center j * q j| ≤ P.center j := by
    rw [abs_mul, abs_of_nonneg (hcenterNonneg j)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hq j) (hcenterNonneg j)
  have htotal :
      (∑ r : BandPrime n W, P.center (P.band r) / (r.1 : ℝ)) = T := by
    calc
      (∑ r : BandPrime n W, P.center (P.band r) / (r.1 : ℝ)) =
          ∑ j : Band, P.mass j * P.center j := by
        rw [← Finset.sum_fiberwise Finset.univ P.band
          (fun r : BandPrime n W ↦ P.center (P.band r) / (r.1 : ℝ))]
        apply Finset.sum_congr rfl
        intro j hj
        change (∑ r ∈ P.data.fiber j,
          P.center (P.band r) / (r.1 : ℝ)) = P.mass j * P.center j
        calc
          _ = ∑ r ∈ P.data.fiber j,
              (1 / (r.1 : ℝ)) * P.center j := by
            apply Finset.sum_congr rfl
            intro r hr
            have hrj : P.band r = j := by
              simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
                using hr
            rw [hrj]
            ring
          _ = P.mass j * P.center j := by
            rw [← Finset.sum_mul]
            rfl
      _ = T := by
        exact P.sum_mass_mul_center_eq_bandTReciprocalSum
  have hentry (p r : BandPrime n W) :
      |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤
        (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) +
        (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
            (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) ^ 2 +
        (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) ^ 2 +
        (if p = r then
          3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2
        else 0) := by
    by_cases hpr : p = r
    · subst r
      rw [if_pos rfl]
      have hdiag :=
        abs_covVV_sub_covII_le_of_transferBounds_diagonal law h75 p
      have hoffNonneg : 0 ≤
          (Cpow * tPrime n p.1 * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) +
          (Cpow * tPrime n p.1 * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) ^ 2 +
          (Cpow * tPrime n p.1 * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) ^ 2 := by
        have hc : 0 ≤ Cpow * tPrime n p.1 * tPrime n p.1 + epsilon := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg hCpow (htNonneg p)) (htNonneg p))
            hepsilon
        positivity
      linarith
    · rw [if_neg hpr, add_zero]
      exact abs_covVV_sub_covII_le_of_transferBounds_of_ne law h75 p r hpr
  have hbase (p : BandPrime n W) : 0 ≤
      (Cpow * tPrime n p.1 + epsilon) * T *
        (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
    have hc : 0 ≤ Cpow * tPrime n p.1 + epsilon :=
      add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon
    positivity
  have hinner (p : BandPrime n W) :
      (∑ r : BandPrime n W,
        |P.center (P.band r) * q (P.band r)| *
          |law.covVV p.1 r.1 - law.covII p.1 r.1|) ≤
        3 * ((Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) +
        3 * (Cpow + epsilon) * P.center (P.band p) *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
    let JI : BandPrime n W → ℝ := fun r ↦
      (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ))
    let IJ : BandPrime n W → ℝ := fun r ↦
      (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
        (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) ^ 2
    let JJ : BandPrime n W → ℝ := fun r ↦
      (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) ^ 2
    let D : BandPrime n W → ℝ := fun r ↦
      if p = r then 3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0
    have hraw :
        (∑ r : BandPrime n W,
          |P.center (P.band r) * q (P.band r)| *
            |law.covVV p.1 r.1 - law.covII p.1 r.1|) ≤
          ∑ r : BandPrime n W,
            P.center (P.band r) * (JI r + IJ r + JJ r + D r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul (hcoeff (P.band r)) (by
          simpa only [JI, IJ, JJ, D] using hentry p r)
        (abs_nonneg _) (hcenterNonneg (P.band r))
    have hcoef (r : BandPrime n W) :
        Cpow * tPrime n p.1 * tPrime n r.1 + epsilon ≤
          Cpow * tPrime n p.1 + epsilon := by
      have hcp : 0 ≤ Cpow * tPrime n p.1 := mul_nonneg hCpow (htNonneg p)
      nlinarith [htOne r]
    have hJI : (∑ r : BandPrime n W,
        P.center (P.band r) * JI r) ≤
        (Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            (Cpow * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 *
                (P.center (P.band r) / (r.1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 ≤ P.center (P.band r) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) :=
            mul_nonneg
              (mul_nonneg (hcenterNonneg (P.band r)) (sq_nonneg _))
              (hprimeInvNonneg r)
          have hm := mul_le_mul_of_nonneg_right (hcoef r) hfac
          simpa only [JI] using (show
            P.center (P.band r) * JI r ≤
              (Cpow * tPrime n p.1 + epsilon) *
                (1 / (p.1 : ℝ)) ^ 2 *
                  (P.center (P.band r) / (r.1 : ℝ)) by
            dsimp only [JI]
            convert hm using 1 <;> ring)
        _ = (Cpow * tPrime n p.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * T := by
          rw [← Finset.mul_sum, htotal]
        _ ≤ (Cpow * tPrime n p.1 + epsilon) * T *
            (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
          have hcT : 0 ≤ (Cpow * tPrime n p.1 + epsilon) * T :=
            mul_nonneg
              (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon) hT
          have hpSq : (1 / (p.1 : ℝ)) ^ 2 ≤
              (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
            calc
              (1 / (p.1 : ℝ)) ^ 2 =
                  (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by ring
              _ ≤ (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hprimeInvW p)
                  (hprimeInvNonneg p)
          nlinarith [mul_le_mul_of_nonneg_left hpSq hcT]
    have hIJ : (∑ r : BandPrime n W,
        P.center (P.band r) * IJ r) ≤
        (Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            (Cpow * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) * (1 / (W : ℝ)) *
                (P.center (P.band r) / (r.1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 ≤ P.center (P.band r) *
              (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) ^ 2 :=
            mul_nonneg
              (mul_nonneg (hcenterNonneg (P.band r)) (hprimeInvNonneg p))
              (sq_nonneg _)
          have hm := mul_le_mul_of_nonneg_right (hcoef r) hfac
          have hrsq : (1 / (r.1 : ℝ)) ^ 2 ≤
              (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) := by
            calc
              (1 / (r.1 : ℝ)) ^ 2 =
                  (1 / (r.1 : ℝ)) * (1 / (r.1 : ℝ)) := by ring
              _ ≤ (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hprimeInvW r)
                  (hprimeInvNonneg r)
          have hc : 0 ≤ (Cpow * tPrime n p.1 + epsilon) *
              P.center (P.band r) * (1 / (p.1 : ℝ)) :=
            mul_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon)
                (hcenterNonneg (P.band r)))
              (hprimeInvNonneg p)
          dsimp only [IJ]
          calc
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) *
                  (1 / (r.1 : ℝ)) ^ 2 := by nlinarith [hm]
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) *
                  ((1 / (W : ℝ)) * (1 / (r.1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hrsq hc
            _ = _ := by ring
        _ = _ := by
          rw [← Finset.mul_sum, htotal]
          ring
    have hJJ : (∑ r : BandPrime n W,
        P.center (P.band r) * JJ r) ≤
        (Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            (Cpow * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (W : ℝ)) *
                (P.center (P.band r) / (r.1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 ≤ P.center (P.band r) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) ^ 2 := by
            exact mul_nonneg
              (mul_nonneg (hcenterNonneg (P.band r)) (sq_nonneg _))
              (sq_nonneg _)
          have hm := mul_le_mul_of_nonneg_right (hcoef r) hfac
          have hrsq : (1 / (r.1 : ℝ)) ^ 2 ≤
              (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) := by
            calc
              (1 / (r.1 : ℝ)) ^ 2 =
                  (1 / (r.1 : ℝ)) * (1 / (r.1 : ℝ)) := by ring
              _ ≤ (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hprimeInvW r)
                  (hprimeInvNonneg r)
          have hc : 0 ≤ (Cpow * tPrime n p.1 + epsilon) *
              P.center (P.band r) * (1 / (p.1 : ℝ)) ^ 2 :=
            mul_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon)
                (hcenterNonneg (P.band r)))
              (sq_nonneg _)
          dsimp only [JJ]
          calc
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) ^ 2 *
                  (1 / (r.1 : ℝ)) ^ 2 := by nlinarith [hm]
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) ^ 2 *
                  ((1 / (W : ℝ)) * (1 / (r.1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hrsq hc
            _ = _ := by ring
        _ = (Cpow * tPrime n p.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (W : ℝ)) * T := by
          rw [← Finset.mul_sum, htotal]
        _ ≤ _ := by
          have hcTW : 0 ≤ (Cpow * tPrime n p.1 + epsilon) *
              T * (1 / (W : ℝ)) :=
            mul_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon) hT)
              hWinvNonneg
          have hpSq : (1 / (p.1 : ℝ)) ^ 2 ≤
              1 / (p.1 : ℝ) := by
            have hpOne : (1 / (p.1 : ℝ)) ≤ 1 :=
              (hprimeInvW p).trans hWinvOne
            nlinarith [hprimeInvNonneg p]
          nlinarith [mul_le_mul_of_nonneg_left hpSq hcTW]
    have hD : (∑ r : BandPrime n W,
        P.center (P.band r) * D r) ≤
        3 * (Cpow + epsilon) * P.center (P.band p) *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      have hsum : (∑ r : BandPrime n W,
          P.center (P.band r) * D r) =
          3 * (Cpow + epsilon) * P.center (P.band p) *
            (1 / (p.1 : ℝ)) ^ 2 := by
        dsimp only [D]
        calc
          _ = ∑ r : BandPrime n W,
              if r = p then
                P.center (P.band r) *
                  (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2)
              else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hpr : p = r
            · subst r; simp
            · have hrp : r ≠ p := fun h ↦ hpr h.symm
              simp [hpr, hrp]
          _ = P.center (P.band p) *
              (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2) := by
            simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          _ = _ := by ring
      rw [hsum]
      have hc : 0 ≤ 3 * (Cpow + epsilon) * P.center (P.band p) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (add_nonneg hCpow hepsilon))
          (hcenterNonneg (P.band p))
      have hpSq : (1 / (p.1 : ℝ)) ^ 2 ≤
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
        calc
          (1 / (p.1 : ℝ)) ^ 2 =
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by ring
          _ ≤ (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hprimeInvW p) (hprimeInvNonneg p)
      nlinarith [mul_le_mul_of_nonneg_left hpSq hc]
    calc
      _ ≤ ∑ r : BandPrime n W,
          P.center (P.band r) * (JI r + IJ r + JJ r + D r) := hraw
      _ = (∑ r : BandPrime n W, P.center (P.band r) * JI r) +
          (∑ r : BandPrime n W, P.center (P.band r) * IJ r) +
          (∑ r : BandPrime n W, P.center (P.band r) * JJ r) +
          (∑ r : BandPrime n W, P.center (P.band r) * D r) := by
        simp_rw [mul_add]
        simp only [Finset.sum_add_distrib]
      _ ≤ _ := by linarith [hJI, hIJ, hJJ, hD]
  have hfiberBand (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
      P.band p = i := by
    simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
  have hmoment :
      (∑ p ∈ P.data.fiber i,
        tPrime n p.1 * (1 / (p.1 : ℝ))) = P.mass i * P.center i := by
    change (∑ p ∈ P.data.fiber i,
        tPrime n p.1 * (1 / (p.1 : ℝ))) =
      P.mass i *
        ((∑ p ∈ P.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass i)
    have hreorder : (∑ p ∈ P.data.fiber i,
        tPrime n p.1 * (1 / (p.1 : ℝ))) =
        ∑ p ∈ P.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hreorder]
    field_simp [hmass.ne']
  unfold fullSharpRow squarefreeSharpRow fullBandRow squarefreeBandRow
  rw [← sub_div]
  have hraw :
      |(1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covVV p.1 r.1) -
        (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covII p.1 r.1)| ≤
        3 * (Cpow * P.center i + epsilon) * T * (1 / (W : ℝ)) +
          3 * (Cpow + epsilon) * P.center i * (1 / (W : ℝ)) := by
    let A : ℝ := ∑ p ∈ P.data.fiber i,
      ∑ r : BandPrime n W,
        P.center (P.band r) * q (P.band r) * law.covVV p.1 r.1
    let R : ℝ := ∑ p ∈ P.data.fiber i,
      ∑ r : BandPrime n W,
        P.center (P.band r) * q (P.band r) * law.covII p.1 r.1
    have hdiff : A - R = ∑ p ∈ P.data.fiber i,
        ∑ r : BandPrime n W,
          P.center (P.band r) * q (P.band r) *
            (law.covVV p.1 r.1 - law.covII p.1 r.1) := by
      dsimp only [A, R]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have hsum : |A - R| ≤
        (3 * (Cpow * P.center i + epsilon) * T * (1 / (W : ℝ)) +
          3 * (Cpow + epsilon) * P.center i * (1 / (W : ℝ))) *
            P.mass i := by
      rw [hdiff]
      calc
        _ ≤ ∑ p ∈ P.data.fiber i,
            |∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) *
                (law.covVV p.1 r.1 - law.covII p.1 r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ P.data.fiber i,
            (3 * ((Cpow * tPrime n p.1 + epsilon) * T *
              (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) +
            3 * (Cpow + epsilon) * P.center (P.band p) *
              (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          calc
            _ ≤ ∑ r : BandPrime n W,
                |P.center (P.band r) * q (P.band r)| *
                  |law.covVV p.1 r.1 - law.covII p.1 r.1| := by
              calc
                _ ≤ ∑ r : BandPrime n W,
                    |P.center (P.band r) * q (P.band r) *
                      (law.covVV p.1 r.1 - law.covII p.1 r.1)| :=
                  Finset.abs_sum_le_sum_abs _ _
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  rw [abs_mul]
            _ ≤ _ := hinner p
        _ = (3 * (Cpow * P.center i + epsilon) * T *
              (1 / (W : ℝ)) +
            3 * (Cpow + epsilon) * P.center i *
              (1 / (W : ℝ))) * P.mass i := by
          have hmassDef : (∑ p ∈ P.data.fiber i,
              1 / (p.1 : ℝ)) = P.mass i := rfl
          have hdiagFiber :
              (∑ p ∈ P.data.fiber i,
                3 * (Cpow + epsilon) * P.center (P.band p) *
                  (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) =
              ∑ p ∈ P.data.fiber i,
                3 * (Cpow + epsilon) * P.center i *
                  (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [hfiberBand p hp]
          rw [Finset.sum_add_distrib]
          rw [hdiagFiber]
          rw [show (∑ p ∈ P.data.fiber i,
              3 * ((Cpow * tPrime n p.1 + epsilon) * T *
                (1 / (W : ℝ)) * (1 / (p.1 : ℝ)))) =
              3 * (Cpow * P.center i + epsilon) * T *
                (1 / (W : ℝ)) * P.mass i by
            have hbaseSum : (∑ p ∈ P.data.fiber i,
                (Cpow * tPrime n p.1 + epsilon) *
                  (1 / (p.1 : ℝ))) =
                Cpow * (P.mass i * P.center i) + epsilon * P.mass i := by
              have hCsum : (∑ p ∈ P.data.fiber i,
                  Cpow * tPrime n p.1 * (1 / (p.1 : ℝ))) =
                  Cpow * (P.mass i * P.center i) := by
                calc
                  _ = Cpow * (∑ p ∈ P.data.fiber i,
                      tPrime n p.1 * (1 / (p.1 : ℝ))) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro p hp
                    ring
                  _ = _ := by rw [hmoment]
              have hEsum : (∑ p ∈ P.data.fiber i,
                  epsilon * (1 / (p.1 : ℝ))) =
                  epsilon * P.mass i := by
                calc
                  _ = epsilon * (∑ p ∈ P.data.fiber i,
                      1 / (p.1 : ℝ)) := by rw [Finset.mul_sum]
                  _ = _ := by rw [hmassDef]
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib, hCsum, hEsum]
            calc
              _ = 3 * T * (1 / (W : ℝ)) *
                  (∑ p ∈ P.data.fiber i,
                    (Cpow * tPrime n p.1 + epsilon) *
                      (1 / (p.1 : ℝ))) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p hp
                ring
              _ = _ := by rw [hbaseSum]; ring]
          rw [show (∑ p ∈ P.data.fiber i,
              3 * (Cpow + epsilon) * P.center i *
                (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) =
              3 * (Cpow + epsilon) * P.center i *
                (1 / (W : ℝ)) * P.mass i by
            rw [← Finset.mul_sum, hmassDef]]
          ring
    have hscaled : |(1 / P.mass i) * A - (1 / P.mass i) * R| =
        (1 / P.mass i) * |A - R| := by
      rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hmass)]
    change |(1 / P.mass i) * A - (1 / P.mass i) * R| ≤ _
    rw [hscaled]
    calc
      _ ≤ (1 / P.mass i) *
          ((3 * (Cpow * P.center i + epsilon) * T *
              (1 / (W : ℝ)) +
            3 * (Cpow + epsilon) * P.center i *
              (1 / (W : ℝ))) * P.mass i) :=
        mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hmass.le)
      _ = _ := by field_simp [hmass.ne']
  change
    |((1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covVV p.1 r.1) -
        (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covII p.1 r.1)) /
        P.center i| ≤ _
  rw [abs_div, abs_of_pos hcenter]
  calc
    _ ≤ (3 * (Cpow * P.center i + epsilon) * T *
          (1 / (W : ℝ)) +
        3 * (Cpow + epsilon) * P.center i *
          (1 / (W : ℝ))) / P.center i :=
      div_le_div_of_nonneg_right hraw hcenter.le
    _ = 3 * Cpow * (T + 1) * (1 / (W : ℝ)) +
        3 * epsilon * (T / P.center i + 1) *
          (1 / (W : ℝ)) := by
      field_simp [hcenter.ne']
      ring
    _ = 3 * Cpow * (bandTReciprocalSum n W + 1) *
          (1 / (W : ℝ)) +
        3 * epsilon *
          (bandTReciprocalSum n W / P.center i + 1) *
            (1 / (W : ℝ)) := by rfl

end

end Erdos390.Full.PrimePowerSharpBandTransfer

end

universe u_1 u_2
theorem solution :
∀ {Omega : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Omega] [inst_1 : Fintype.{u_2} Band]
  [inst_2 : DecidableEq.{u_2 + 1} Band] {M n W : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M)
  (P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_2} n W Band),
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      ∀ {Cpow epsilon : Real},
        LE.le.{0} (0 : Real) Cpow →
          LE.le.{0} (0 : Real) epsilon →
            Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_1} law n W Cpow epsilon →
              ∀ (q : Band → Real),
                (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
                  ∀ (i : Band),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.PrimePowerSharpBandTransfer.fullSharpRow.{u_1, u_2} law P q i)
                          (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_2} law P q i)))
                      (HAdd.hAdd.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) Cpow)
                            (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W) (1 : Real)))
                          (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) epsilon)
                            (HAdd.hAdd.{0, 0, 0}
                              (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W)
                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2} P i))
                              (1 : Real)))
                          (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))) := by
  exact @Erdos390.Full.PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le
