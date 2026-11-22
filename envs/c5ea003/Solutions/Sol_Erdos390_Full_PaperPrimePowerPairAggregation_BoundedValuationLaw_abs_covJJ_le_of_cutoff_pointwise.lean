-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.abs_covJJ_le_of_cutoff_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:22:55.713781+00:00
-- url     : https://prove2.me/submissions/73703a81-c715-4643-9b88-900abbf7e892

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

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





private theorem summable_linearHalfTerm : Summable linearHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  convert hlin.add hconst using 1
  funext i
  unfold linearHalfTerm
  ring

private theorem tsum_linearHalfTerm_eq_eight :
    ∑' i : ℕ, linearHalfTerm i = 8 := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  rw [show linearHalfTerm = fun i : ℕ ↦
      (i : ℝ) * (1 / (2 : ℝ)) ^ i +
        3 * (1 / (2 : ℝ)) ^ i by
    funext i
    unfold linearHalfTerm
    ring]
  rw [hlin.tsum_add hconst,
    tsum_coe_mul_geometric_of_norm_lt_one hx,
    tsum_mul_left, tsum_geometric_two]
  norm_num

/-- Shifted arithmetic--geometric tails have an absolute numerical bound.
This is the aggregate `r+1` ledger used below. -/
theorem sum_shifted_linear_half_le_eight (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) ≤ 8 := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s, ((r : ℝ) + 1) *
          (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, linearHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      unfold linearHalfTerm g
      norm_num only [Nat.cast_sub hr2]
      ring
    · exact hinj
  rw [heq]
  exact (summable_linearHalfTerm.sum_le_tsum (s.image g)
      (fun i hi ↦ by unfold linearHalfTerm; positivity)).trans_eq
    tsum_linearHalfTerm_eq_eight



/-- The complete finite `r+1` reciprocal-power ledger begins at `p^{-2}`
with an absolute constant. -/
theorem sum_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) / (p : ℝ) ^ r) ≤
      8 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hnum : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) ≤
            ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2)) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * 8 :=
      mul_le_mul_of_nonneg_left (sum_shifted_linear_half_le_eight R)
        (by positivity)
    _ = 8 / (p : ℝ) ^ 2 := by ring



























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

/- Source module: Erdos390.Full.PaperPrimePowerPairAggregation -/
section


/-!
# From actual prime-power pairs to a paper prime row

This file performs the finite aggregation that follows the pointwise
two-local estimates in Lemma 7.5.  Its inputs are covariances and moments of
the genuine divisor-indicator columns of an actual `BoundedValuationLaw`.
The preceding logarithmic-cutoff module makes every exponent range literal.

The factors `8`, `64`, and `quadraticHalfMass` are obtained from the proved
geometric series, rather than hidden in an `O`-constant.  A single universal
aggregation constant then feeds the already formalized paper-band row
contraction.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerPairAggregation

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff
open PrimeSums
open PaperPrimePowerRow

noncomputable section











namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)





/-- The genuine double-high covariance contracts to `p^{-2}q^{-2}`. -/
theorem abs_covJJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) + e r s) :
    |law.covJJ p q| ≤
      64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
  rw [covJJ_eq_valuationCutoff_sum law hp hq]
  calc
    |∑ r ∈ highExponents (valuationCutoff p M),
        ∑ s ∈ highExponents (valuationCutoff q M),
          law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M),
            |law.probability.covariance (law.Ip p r) (law.Ip q s)| := by
      calc
        _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
            |∑ s ∈ highExponents (valuationCutoff q M),
              law.probability.covariance (law.Ip p r) (law.Ip q s)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M),
            (K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
              ((p : ℝ) ^ r * (q : ℝ) ^ s)) + e r s) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.sum_le_sum fun s hs ↦ hpoint r hr s hs
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            ((r : ℝ) + 1) / (p : ℝ) ^ r) *
          (∑ s ∈ highExponents (valuationCutoff q M),
            ((s : ℝ) + 1) / (q : ℝ) ^ s) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M),
              K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
                ((p : ℝ) ^ r * (q : ℝ) ^ s))) =
            ∑ r ∈ highExponents (valuationCutoff p M),
              (K * (((r : ℝ) + 1) / (p : ℝ) ^ r)) *
                (∑ s ∈ highExponents (valuationCutoff q M),
                  ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = K *
            (∑ r ∈ highExponents (valuationCutoff p M),
              ((r : ℝ) + 1) / (p : ℝ) ^ r) *
            (∑ s ∈ highExponents (valuationCutoff q M),
              ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
      have hsumP := sum_raddone_inv_pow_le
        (R := valuationCutoff p M) hp.two_le
      have hsumQ := sum_raddone_inv_pow_le
        (R := valuationCutoff q M) hq.two_le
      have hSP0 : 0 ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          ((r : ℝ) + 1) / (p : ℝ) ^ r := by positivity
      have hSQ0 : 0 ≤ ∑ s ∈ highExponents (valuationCutoff q M),
          ((s : ℝ) + 1) / (q : ℝ) ^ s := by positivity
      have hAP0 : 0 ≤ 8 / (p : ℝ) ^ 2 := by positivity
      have hmain :
          K * (∑ r ∈ highExponents (valuationCutoff p M),
              ((r : ℝ) + 1) / (p : ℝ) ^ r) *
              (∑ s ∈ highExponents (valuationCutoff q M),
                ((s : ℝ) + 1) / (q : ℝ) ^ s) ≤
            K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) := by
        calc
          _ ≤ K * (8 / (p : ℝ) ^ 2) *
              (∑ s ∈ highExponents (valuationCutoff q M),
                ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsumP hK) hSQ0
          _ ≤ K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hsumQ (mul_nonneg hK hAP0)
      exact add_le_add hmain le_rfl
    _ = 64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
          ∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
      ring





end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

universe u_1
theorem solution :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] {M : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M) {p q : Nat},
  Nat.Prime p →
    Nat.Prime q →
      ∀ {K : Real},
        LE.le.{0} (0 : Real) K →
          ∀ (e : Nat → Nat → Real),
            (∀ (r : Nat),
                Membership.mem.{0, 0}
                    (Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                    r →
                  ∀ (s : Nat),
                    Membership.mem.{0, 0}
                        (Erdos390.Full.ArithmeticModel.highExponents
                          (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                        s →
                      LE.le.{0}
                        (abs.{0}
                          (Erdos390.Full.FiniteProbability.covariance.{u_1}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q s)))
                        (HAdd.hAdd.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} K
                            (HDiv.hDiv.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real)))
                              (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) (HPow.hPow.{0, 0, 0} (↑q) s))))
                          (e r s))) →
              LE.le.{0} (abs.{0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covJJ.{u_1} law p q))
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (64 : Real) K)
                      (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat)))
                  (∑
                    r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                    ∑
                      s ∈
                        Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                      e r s)) := by
  exact @Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.abs_covJJ_le_of_cutoff_pointwise
