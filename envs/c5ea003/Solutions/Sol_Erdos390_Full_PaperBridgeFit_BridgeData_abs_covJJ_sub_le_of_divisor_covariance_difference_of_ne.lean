-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:14:44.805839+00:00
-- url     : https://prove2.me/submissions/8843933c-3c7f-4c37-87a4-ab25dd76a05f

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002

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

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section

private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb

/-- Every finite shifted half-geometric tail is bounded by the complete
geometric series. -/
theorem sum_shifted_half_le_two (k A : ℕ) :
    (∑ a ∈ Finset.Icc k A,
        (1 / (2 : ℝ)) ^ (a - k)) ≤ 2 := by
  let s := Finset.Icc k A
  let g : ℕ → ℕ := fun a ↦ a - k
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc k A
  have heq :
      (∑ a ∈ s, (1 / (2 : ℝ)) ^ (a - k)) =
        ∑ i ∈ s.image g, (1 / (2 : ℝ)) ^ i := by
    symm
    rw [Finset.sum_image]
    exact hinj
  rw [heq]
  exact (summable_geometric_two.sum_le_tsum (s.image g)
    (fun i hi ↦ by positivity)).trans_eq tsum_geometric_two









/-- A finite reciprocal-power tail beginning at exponent `r+1` has the
same bound as the corresponding infinite geometric tail. -/
theorem sum_inv_pow_tail_le {p r A : ℕ} (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Icc (r + 1) A,
        (1 / (p : ℝ) ^ (r + 1)) *
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hra : r + 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpPow : (2 : ℝ) ^ (a - (r + 1)) ≤
          (p : ℝ) ^ (a - (r + 1)) := by gcongr
      have haSplit : a = (r + 1) + (a - (r + 1)) := by omega
      have hpowSplit : (p : ℝ) ^ a =
          (p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1)) := by
        conv_lhs => rw [haSplit]
        rw [pow_add]
      norm_num only [Nat.cast_pow]
      rw [hpowSplit]
      calc
        1 / ((p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1))) ≤
            1 / ((p : ℝ) ^ (r + 1) *
              (2 : ℝ) ^ (a - (r + 1))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ (r + 1)) *
            (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ (r + 1)) *
        ∑ a ∈ Finset.Icc (r + 1) A,
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ (r + 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shifted_half_le_two (r + 1) A)
        (by positivity)
    _ = 2 / (p : ℝ) ^ (r + 1) := by ring





























end

end Erdos390.Full.LocalFugacityBounds

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

/- Source module: Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow -/
section


/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





































/-- For distinct primes both higher-valuation tails factor geometrically. -/
theorem abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJJ p q - mu.covJJ p q| ≤
      e * (4 * G + 12 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
  rw [covJJ_eq_valuationCutoff_sum nu hp hq,
    covJJ_eq_valuationCutoff_sum mu hp hq,
    ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        ((∑ l ∈ highExponents (valuationCutoff q M),
            nu.probability.covariance (nu.Ip p k) (nu.Ip q l)) -
          ∑ l ∈ highExponents (valuationCutoff q M),
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |∑ l ∈ highExponents (valuationCutoff q M),
              nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            ∑ l ∈ highExponents (valuationCutoff q M),
              mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ highExponents (valuationCutoff p M),
          |∑ l ∈ highExponents (valuationCutoff q M),
            (nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
              mu.probability.covariance (mu.Ip p k) (mu.Ip q l))| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          |nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((q ^ l : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hcop : Nat.Coprime (p ^ k) (q ^ l) :=
        Nat.coprime_pow_primes k l hp hq hpq
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / ((q ^ l : ℕ) : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip] using
            hcov (p ^ k) (q ^ l) (pow_pos hp.pos k) (pow_pos hq.pos l)
        _ = e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((q ^ l : ℕ) : ℝ)) := by
          rw [hcop.lcm_eq_mul, Nat.cast_mul]
          ring
    _ = (e * (G + 3 * G ^ 2)) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) *
        (∑ l ∈ highExponents (valuationCutoff q M),
          1 / ((q ^ l : ℕ) : ℝ)) := by
      calc
        (∑ k ∈ highExponents (valuationCutoff p M),
          ∑ l ∈ highExponents (valuationCutoff q M),
            e * (G + 3 * G ^ 2) *
              (1 / ((p ^ k : ℕ) : ℝ)) *
                (1 / ((q ^ l : ℕ) : ℝ))) =
            ∑ k ∈ highExponents (valuationCutoff p M),
              (e * (G + 3 * G ^ 2) *
                (1 / ((p ^ k : ℕ) : ℝ))) *
                (∑ l ∈ highExponents (valuationCutoff q M),
                  1 / ((q ^ l : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
        _ = (∑ k ∈ highExponents (valuationCutoff p M),
              e * (G + 3 * G ^ 2) *
                (1 / ((p ^ k : ℕ) : ℝ))) *
              (∑ l ∈ highExponents (valuationCutoff q M),
                1 / ((q ^ l : ℕ) : ℝ)) := by
            rw [Finset.sum_mul]
        _ = _ := by
            rw [← Finset.mul_sum]
    _ ≤ (e * (G + 3 * G ^ 2)) *
        (2 / (p : ℝ) ^ 2) * (2 / (q : ℝ) ^ 2) := by
      have hpTail := sum_inv_pow_tail_le (p := p) (r := 1)
        (A := valuationCutoff p M) hp.two_le
      have hqTail := sum_inv_pow_tail_le (p := q) (r := 1)
        (A := valuationCutoff q M) hq.two_le
      have hcoef : 0 ≤ e * (G + 3 * G ^ 2) := by positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (by simpa only [highExponents] using hpTail)
          hcoef)
        (by simpa only [highExponents] using hqTail)
        (by positivity) (by positivity)
    _ = e * (4 * G + 12 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by ring

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_3 u_4
theorem solution :
∀ {Omega : Type u_3} {Theta : Type u_4} [inst : Fintype.{u_3} Omega] [inst_1 : Fintype.{u_4} Theta] {M p q : Nat}
  (nu : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} Omega M)
  (mu : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_4} Theta M),
  Nat.Prime p →
    Nat.Prime q →
      Ne.{1} p q →
        ∀ {e G : Real},
          LE.le.{0} (0 : Real) e →
            LE.le.{0} (0 : Real) G →
              (∀ (D E : Nat),
                  LT.lt.{0} (0 : Nat) D →
                    LT.lt.{0} (0 : Nat) E →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.covariance.{u_3}
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_3} nu)
                              (fun x =>
                                Erdos390.Full.ArithmeticModel.divInd D
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_3} nu x))
                              fun x =>
                              Erdos390.Full.ArithmeticModel.divInd E
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_3} nu x))
                            (Erdos390.Full.FiniteProbability.covariance.{u_4}
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} mu)
                              (fun x =>
                                Erdos390.Full.ArithmeticModel.divInd D
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} mu x))
                              fun x =>
                              Erdos390.Full.ArithmeticModel.divInd E
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} mu x))))
                        (HMul.hMul.{0, 0, 0} e
                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑(Nat.lcm D E)))
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (3 : Real)
                                (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑D)))
                              (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑E)))))) →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covJJ.{u_3} nu p q)
                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covJJ.{u_4} mu p q)))
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0} e
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) G)
                          (HMul.hMul.{0, 0, 0} (12 : Real) (HPow.hPow.{0, 0, 0} G (2 : Nat)))))
                      (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
