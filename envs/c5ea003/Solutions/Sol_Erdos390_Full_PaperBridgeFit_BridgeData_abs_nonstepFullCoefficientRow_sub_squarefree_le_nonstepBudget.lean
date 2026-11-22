-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:14:11.050717+00:00
-- url     : https://prove2.me/submissions/8b9c265f-2832-486f-af1b-85e4db5e68b6

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



end

end Erdos390.Full.PrimePowerSharpBandTransfer

end

/- Source module: Erdos390.Full.PaperNonstepSlowRightLedger -/
section


/-!
# Exact non-step prime-power ledger for the slow right row

The slow coefficient is the literal arithmetic deviation
`g_p = alpha_{j(p)} - t_p`; it is not replaced by a step function.  This
file keeps the `t_p` factors in the three `JI/IJ/JJ` orientations until
after the output-band average.  The resulting finite estimate has exactly
three kinds of terms:

* a structural `Cpow / W` multiple of `w * alpha_i`;
* an analytic remainder `epsilon / W` times `w` (to be divided by the
  actual arithmetic centre only in the eventual specialization); and
* the literal local reciprocal-square deviation ledger.

No mesh, continuum centre, asymptotic profile, or ODE box occurs in the
theorem below.  It is therefore reusable in both Lemma 8.6 and Proposition
8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

namespace BridgeData

private theorem normalized_double_sum_factor
    {P Q : Type*} [Fintype Q]
    (H : ℝ) (s : Finset P) (f : P → ℝ) (g : Q → ℝ) :
    (1 / H) * ∑ p ∈ s, ∑ q : Q, f p * g q =
      ((1 / H) * ∑ p ∈ s, f p) * ∑ q : Q, g q := by
  have hinner (p : P) :
      (∑ q : Q, f p * g q) = f p * ∑ q : Q, g q := by
    rw [Finset.mul_sum]
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  ring

private theorem normalized_double_sum_factor_const
    {P Q : Type*} [Fintype Q]
    (H : ℝ) (s : Finset P) (c : ℝ) (f : P → ℝ) (g : Q → ℝ) :
    (1 / H) * ∑ p ∈ s, ∑ q : Q, c * f p * g q =
      c * ((1 / H) * ∑ p ∈ s, f p) * ∑ q : Q, g q := by
  have hinner (p : P) :
      (∑ q : Q, c * f p * g q) =
        c * ∑ q : Q, f p * g q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  calc
    (1 / H) * (c * ∑ p ∈ s, ∑ q : Q, f p * g q) =
        c * ((1 / H) * ∑ p ∈ s, ∑ q : Q, f p * g q) := by ring
    _ = c * ((1 / H) * ∑ p ∈ s, f p) * ∑ q : Q, g q := by
      rw [normalized_double_sum_factor H s f g]
      ring

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















set_option maxHeartbeats 3000000 in
/-- **Exact non-step slow-row ledger.**

The constant `21` is the sum of the three orientation constants `7`; no
factor depending on a mesh, a low centre, or a tilt box is hidden in it.
The only term not already proportional to the actual output centre is the
explicit `epsilon / W` remainder.  The diagonal is not bounded crudely by
`1/W`: its literal local value is exported for the moving-low-cell
specialization. -/
theorem abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
    {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw)
    {Cpow epsilon w : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon) (hw : 0 ≤ w)
    (hW : 1 < B.sampleData.W)
    (h75 : PrimePowerTransferBounds law
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.nonstepFullCoefficientRow law i -
        B.nonstepSquarefreeCoefficientRow law i| ≤
      nonstepPrimePowerRowBudget Cpow epsilon w
        (B.sampleData.W : ℝ) (B.bandCenter i)
        (B.bandDeviationReciprocalSquare i) := by
  let H := B.harmonicMass i
  let alpha := B.bandCenter i
  let invW : ℝ := 1 / (B.sampleData.W : ℝ)
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by simpa only [alpha] using B.bandCenter_pos i
  have hWreal : (0 : ℝ) < B.sampleData.W := by
    exact_mod_cast Nat.zero_lt_of_lt hW
  have hinvW0 : 0 ≤ invW := by dsimp only [invW]; positivity
  have hinvW1 : invW ≤ 1 := by
    dsimp only [invW]
    have hOne : (1 : ℝ) ≤ B.sampleData.W := by exact_mod_cast hW.le
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hOne
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hpInv0 (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ (1 / (p.1 : ℝ)) := by positivity
  have hpInvW (p : BandPrime B.sampleData.n B.sampleData.W) :
      (1 / (p.1 : ℝ)) ≤ invW := by
    exact one_div_le_one_div_of_le hWreal
      (by exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le)
  have ht0 (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ tPrime B.sampleData.n p.1 :=
    PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one p.2
  have ht1 (p : BandPrime B.sampleData.n B.sampleData.W) :
      tPrime B.sampleData.n p.1 ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one p.2
  let B1 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    |B.primeDeviation q| * (1 / (q.1 : ℝ))
  let G1 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
      (1 / (q.1 : ℝ))
  let B2 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2
  let G2 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
      (1 / (q.1 : ℝ)) ^ 2
  have hB1 : B1 ≤ 7 * w := by
    simpa only [B1, primeDeviationL1, mul_comm] using hdevL1
  have hB10 : 0 ≤ B1 := by
    dsimp only [B1]
    exact Finset.sum_nonneg fun q _hq ↦ mul_nonneg (abs_nonneg _) (hpInv0 q)
  have hG10 : 0 ≤ G1 := by
    dsimp only [G1]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (mul_nonneg (ht0 q) (abs_nonneg _)) (hpInv0 q)
  have hB20 : 0 ≤ B2 := by
    dsimp only [B2]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hG20 : 0 ≤ G2 := by
    dsimp only [G2]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (mul_nonneg (ht0 q) (abs_nonneg _)) (sq_nonneg _)
  have hG1 : G1 ≤ B1 := by
    dsimp only [G1, B1]
    apply Finset.sum_le_sum
    intro q _hq
    have hfac : 0 ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) :=
      mul_nonneg (abs_nonneg _) (hpInv0 q)
    nlinarith [mul_le_mul_of_nonneg_right (ht1 q) hfac]
  have hB2 : B2 ≤ invW * B1 := by
    dsimp only [B2, B1]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _hq
    have hmul := mul_le_mul_of_nonneg_left (hpInvW q) (abs_nonneg (B.primeDeviation q))
    calc
      |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2 =
          |B.primeDeviation q| * (1 / (q.1 : ℝ)) *
            (1 / (q.1 : ℝ)) := by ring
      _ ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) * invW :=
        mul_le_mul_of_nonneg_left (hpInvW q)
          (mul_nonneg (abs_nonneg _) (hpInv0 q))
      _ = invW * (|B.primeDeviation q| * (1 / (q.1 : ℝ))) := by ring
  have hG2 : G2 ≤ B2 := by
    dsimp only [G2, B2]
    apply Finset.sum_le_sum
    intro q _hq
    have hfac : 0 ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2 :=
      mul_nonneg (abs_nonneg _) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right (ht1 q) hfac]
  have hG1w : G1 ≤ 7 * w := hG1.trans hB1
  have hB2w : B2 ≤ 7 * invW * w := by
    calc
      B2 ≤ invW * B1 := hB2
      _ ≤ invW * (7 * w) := mul_le_mul_of_nonneg_left hB1 hinvW0
      _ = 7 * invW * w := by ring
  have hG2w : G2 ≤ 7 * invW * w := hG2.trans hB2w
  have hfirst :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) = alpha := by
    change (1 / B.partition.data.mass i) *
        (∑ p ∈ B.partition.data.fiber i,
          tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) =
      (∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
        B.partition.data.mass i
    rw [show (∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) =
        ∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 by
      apply Finset.sum_congr rfl
      intro p _hp
      ring]
    ring
  have hmass :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) = 1 := by
    change (1 / H) * H = 1
    field_simp [ne_of_gt hH]
  have hfirst2 :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2 ≤
          invW * alpha := by
    calc
      _ ≤ (1 / H) * ∑ p ∈ B.partition.data.fiber i,
          invW * (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        calc
          tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2 =
              (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) *
                (1 / (p.1 : ℝ)) := by ring
          _ ≤ (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) * invW :=
            mul_le_mul_of_nonneg_left (hpInvW p)
              (mul_nonneg (ht0 p) (hpInv0 p))
          _ = _ := by ring
      _ = invW * alpha := by
        rw [← Finset.mul_sum]
        calc
          (1 / H) *
              (invW * ∑ p ∈ B.partition.data.fiber i,
                tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) =
              invW * ((1 / H) *
                ∑ p ∈ B.partition.data.fiber i,
                  tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) := by ring
          _ = invW * alpha := by rw [hfirst]
  have hmass2 :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) ^ 2 ≤ invW := by
    calc
      _ ≤ (1 / H) * ∑ p ∈ B.partition.data.fiber i,
          invW * (1 / (p.1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right (hpInvW p) (hpInv0 p)
      _ = invW := by
        rw [← Finset.mul_sum]
        calc
          (1 / H) *
              (invW * ∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ))) =
              invW * ((1 / H) *
                ∑ p ∈ B.partition.data.fiber i,
                  (1 / (p.1 : ℝ))) := by ring
          _ = invW := by rw [hmass, mul_one]
  -- Build the entry display on the diagonal, where the public
  -- off-diagonal theorem intentionally requires `p ≠ q`.
  have hentry' (p q : BandPrime B.sampleData.n B.sampleData.W) :
      |law.covVV p.1 q.1 - law.covII p.1 q.1| ≤
        (Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n q.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
        (Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n q.1 + epsilon) *
            (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
        (Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n q.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
        (if p = q then
          3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0) := by
    by_cases hpq : p = q
    · subst q
      rw [if_pos rfl]
      have hd :=
        PrimePowerSharpBandTransfer.abs_covVV_sub_covII_le_of_transferBounds_diagonal
          law h75 p
      have hoff : 0 ≤
          (Cpow * tPrime B.sampleData.n p.1 *
                tPrime B.sampleData.n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) +
          (Cpow * tPrime B.sampleData.n p.1 *
                tPrime B.sampleData.n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) ^ 2 +
          (Cpow * tPrime B.sampleData.n p.1 *
                tPrime B.sampleData.n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) ^ 2 := by
        have hc : 0 ≤ Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n p.1 + epsilon :=
          add_nonneg
            (mul_nonneg (mul_nonneg hCpow (ht0 p)) (ht0 p)) hepsilon
        positivity
      linarith
    · rw [if_neg hpq]
      simpa only [add_zero] using
        PrimePowerSharpBandTransfer.abs_covVV_sub_covII_le_of_transferBounds_of_ne
          law h75 p q hpq
  unfold nonstepFullCoefficientRow nonstepSquarefreeCoefficientRow
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hdiff :
      (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law.covVV p.1 q.1) -
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law.covII p.1 q.1) =
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                (law.covVV p.1 q.1 - law.covII p.1 q.1) := by
    congr 1
    apply Finset.sum_congr rfl
    intro p _hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  rw [hdiff]
  calc
    |(1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * (law.covVV p.1 q.1 - law.covII p.1 q.1)| ≤
      (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q| *
              |law.covVV p.1 q.1 - law.covII p.1 q.1| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / H : ℝ))]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p _hp ↦
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun q _hq ↦ by rw [abs_mul]))
    _ ≤ (21 * Cpow * invW) * (w * alpha) +
          (21 * epsilon * invW) * w +
          3 * (Cpow + epsilon) * B.bandDeviationReciprocalSquare i := by
      -- Each of `JI`, `IJ`, and `JJ` is contracted separately; the
      -- diagonal remains literal.  `ring_nf` after distributivity leaves
      -- precisely the four moment products proved above.
      have hpoint (p : BandPrime B.sampleData.n B.sampleData.W)
          (q : BandPrime B.sampleData.n B.sampleData.W) :
          |B.primeDeviation q| *
              |law.covVV p.1 q.1 - law.covII p.1 q.1| ≤
            |B.primeDeviation q| *
              ((Cpow * tPrime B.sampleData.n p.1 *
                    tPrime B.sampleData.n q.1 + epsilon) *
                  (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
               (Cpow * tPrime B.sampleData.n p.1 *
                    tPrime B.sampleData.n q.1 + epsilon) *
                  (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
               (Cpow * tPrime B.sampleData.n p.1 *
                    tPrime B.sampleData.n q.1 + epsilon) *
                  (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
               (if p = q then
                  3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left (hentry' p q) (abs_nonneg _)
      calc
        _ ≤ (1 / H) * ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q| *
                ((Cpow * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
                 (Cpow * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
                 (Cpow * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
                 (if p = q then
                    3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun p _hp ↦
            Finset.sum_le_sum fun q _hq ↦ hpoint p q
        _ ≤ _ := by
          let OT1 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))
          let O1 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i, (1 / (p.1 : ℝ))
          let OT2 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2
          let O2 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i, (1 / (p.1 : ℝ)) ^ 2
          let JI : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  ((Cpow * tPrime B.sampleData.n p.1 *
                        tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)))
          let IJ : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  ((Cpow * tPrime B.sampleData.n p.1 *
                        tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2)
          let JJ : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  ((Cpow * tPrime B.sampleData.n p.1 *
                        tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2)
          let D : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  (if p = q then
                    3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0)
          have hsplit :
              (1 / H) * ∑ p ∈ B.partition.data.fiber i,
                ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                  |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
                     (Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
                     (Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
                     (if p = q then 3 * (Cpow + epsilon) *
                        (1 / (p.1 : ℝ)) ^ 2 else 0)) =
                JI + IJ + JJ + D := by
            dsimp only [JI, IJ, JJ, D]
            simp_rw [mul_add, Finset.sum_add_distrib]
            ring
          have hJIeq : JI = Cpow * OT2 * G1 + epsilon * O2 * B1 := by
            have hpointEq (p : BandPrime B.sampleData.n B.sampleData.W)
                (q : BandPrime B.sampleData.n B.sampleData.W) :
                |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                      (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ))) =
                  Cpow *
                    (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2) *
                    (tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
                      (1 / (q.1 : ℝ))) +
                  epsilon * (1 / (p.1 : ℝ)) ^ 2 *
                    (|B.primeDeviation q| * (1 / (q.1 : ℝ))) := by ring
            dsimp only [JI]
            simp_rw [hpointEq, Finset.sum_add_distrib]
            rw [mul_add,
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) Cpow
                (fun p ↦ tPrime B.sampleData.n p.1 *
                  (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ tPrime B.sampleData.n q.1 *
                  |B.primeDeviation q| * (1 / (q.1 : ℝ))),
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) epsilon
                (fun p ↦ (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ |B.primeDeviation q| * (1 / (q.1 : ℝ)))]
          have hIJeq : IJ = Cpow * OT1 * G2 + epsilon * O1 * B2 := by
            have hpointEq (p : BandPrime B.sampleData.n B.sampleData.W)
                (q : BandPrime B.sampleData.n B.sampleData.W) :
                |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                      (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2) =
                  Cpow *
                    (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) *
                    (tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
                      (1 / (q.1 : ℝ)) ^ 2) +
                  epsilon * (1 / (p.1 : ℝ)) *
                    (|B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2) := by ring
            dsimp only [IJ]
            simp_rw [hpointEq, Finset.sum_add_distrib]
            rw [mul_add,
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) Cpow
                (fun p ↦ tPrime B.sampleData.n p.1 *
                  (1 / (p.1 : ℝ)))
                (fun q ↦ tPrime B.sampleData.n q.1 *
                  |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2),
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) epsilon
                (fun p ↦ (1 / (p.1 : ℝ)))
                (fun q ↦ |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2)]
          have hJJeq : JJ = Cpow * OT2 * G2 + epsilon * O2 * B2 := by
            have hpointEq (p : BandPrime B.sampleData.n B.sampleData.W)
                (q : BandPrime B.sampleData.n B.sampleData.W) :
                |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                      (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2) =
                  Cpow *
                    (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2) *
                    (tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
                      (1 / (q.1 : ℝ)) ^ 2) +
                  epsilon * (1 / (p.1 : ℝ)) ^ 2 *
                    (|B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2) := by ring
            dsimp only [JJ]
            simp_rw [hpointEq, Finset.sum_add_distrib]
            rw [mul_add,
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) Cpow
                (fun p ↦ tPrime B.sampleData.n p.1 *
                  (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ tPrime B.sampleData.n q.1 *
                  |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2),
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) epsilon
                (fun p ↦ (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2)]
          have hDeq : D =
              3 * (Cpow + epsilon) * B.bandDeviationReciprocalSquare i := by
            have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
                (∑ q : BandPrime B.sampleData.n B.sampleData.W,
                  |B.primeDeviation q| *
                    (if p = q then 3 * (Cpow + epsilon) *
                      (1 / (p.1 : ℝ)) ^ 2 else 0)) =
                  |B.primeDeviation p| *
                    (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2) := by
              calc
                _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                    if q = p then
                      |B.primeDeviation q| *
                        (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2)
                    else 0 := by
                      apply Finset.sum_congr rfl
                      intro q _hq
                      by_cases hpq : p = q
                      · subst q; simp
                      · have hqp : q ≠ p := fun h ↦ hpq h.symm
                        simp [hpq, hqp]
                _ = _ := by simp
            dsimp only [D]
            simp_rw [hinner]
            rw [show (∑ p ∈ B.partition.data.fiber i,
                |B.primeDeviation p| *
                  (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2)) =
                3 * (Cpow + epsilon) *
                  ∑ p ∈ B.partition.data.fiber i,
                    |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2 by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _hp
              ring]
            unfold bandDeviationReciprocalSquare
            ring
          have hJI : JI ≤
              7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w := by
            rw [hJIeq]
            have hOT2 : OT2 ≤ invW * alpha := by simpa only [OT2] using hfirst2
            have hO2 : O2 ≤ invW := by simpa only [O2] using hmass2
            calc
              Cpow * OT2 * G1 + epsilon * O2 * B1 ≤
                  Cpow * (invW * alpha) * (7 * w) +
                    epsilon * invW * (7 * w) := by gcongr
              _ = _ := by ring
          have hIJ : IJ ≤
              7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w := by
            rw [hIJeq]
            have hOT1 : OT1 = alpha := by simpa only [OT1] using hfirst
            have hO1 : O1 = 1 := by simpa only [O1] using hmass
            rw [hOT1, hO1]
            simp only [mul_one]
            calc
              Cpow * alpha * G2 + epsilon * B2 ≤
                  Cpow * alpha * (7 * invW * w) +
                    epsilon * (7 * invW * w) := by gcongr
              _ = _ := by ring
          have hJJ : JJ ≤
              7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w := by
            rw [hJJeq]
            have hOT2 : OT2 ≤ invW * alpha := by simpa only [OT2] using hfirst2
            have hO2 : O2 ≤ invW := by simpa only [O2] using hmass2
            have hinvSq : invW * invW ≤ invW := by nlinarith
            calc
              Cpow * OT2 * G2 + epsilon * O2 * B2 ≤
                  Cpow * (invW * alpha) * (7 * invW * w) +
                    epsilon * invW * (7 * invW * w) := by gcongr
              _ ≤ 7 * Cpow * invW * w * alpha +
                    7 * epsilon * invW * w := by
                have hca : 0 ≤ 7 * Cpow * w * alpha := by positivity
                have hew : 0 ≤ 7 * epsilon * w := by positivity
                nlinarith [mul_le_mul_of_nonneg_left hinvSq hca,
                  mul_le_mul_of_nonneg_left hinvSq hew]
          rw [hsplit]
          calc
            JI + IJ + JJ + D ≤
                (7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w) +
                (7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w) +
                (7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w) +
                3 * (Cpow + epsilon) *
                  B.bandDeviationReciprocalSquare i :=
              add_le_add (add_le_add (add_le_add hJI hIJ) hJJ) hDeq.le
            _ = (21 * Cpow * invW) * (w * alpha) +
                  (21 * epsilon * invW) * w +
                  3 * (Cpow + epsilon) *
                    B.bandDeviationReciprocalSquare i := by ring
    _ = nonstepPrimePowerRowBudget Cpow epsilon w
          (B.sampleData.W : ℝ) (B.bandCenter i)
          (B.bandDeviationReciprocalSquare i) := by
      simp only [nonstepPrimePowerRowBudget, invW, alpha]



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2 u_3
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {Omega : Type u_3} [inst_4 : Fintype.{u_3} Omega]
  {Mlaw : Nat} (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} Omega Mlaw) {Cpow epsilon w : Real},
  LE.le.{0} (0 : Real) Cpow →
    LE.le.{0} (0 : Real) epsilon →
      LE.le.{0} (0 : Real) w →
        LT.lt.{0} (1 : Nat)
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
          Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_3} law
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              Cpow epsilon →
            LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
                (HMul.hMul.{0, 0, 0} (7 : Real) w) →
              ∀ (i : Band),
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepFullCoefficientRow.{u_1, u_2, u_3} B law i)
                      (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepSquarefreeCoefficientRow.{u_1, u_2, u_3} B law
                        i)))
                  (Erdos390.Full.PaperBridgeFit.BridgeData.nonstepPrimePowerRowBudget Cpow epsilon w
                    (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandDeviationReciprocalSquare.{u_1, u_2} B i)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
