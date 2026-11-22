-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerGenericAggregation.primePowerTransferBounds_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:04:34.504035+00:00
-- url     : https://prove2.me/submissions/b485cdf9-a6c1-4a7b-9fdb-b823be7bbea3

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_PaperPrimePowerPairAggregation_BoundedValuationLaw_paperBand_row_le_of_cutoff_pointwise

/- Source module: Erdos390.Full.PowerLedger -/
section


/-!
# Exact prime-power ledgers

The aggregate prime-power argument uses the pointwise identity
`J_p^2 = ∑_{r≥2} (2r-3) 1_{p^r∣m}`.  This file proves that identity
for the actual valuation and divisibility columns, with a common finite
physical cutoff.  Thus later expectation and covariance manipulations do not
need to treat it as a stylized fact.
-/

open scoped BigOperators

namespace Erdos390.Full.PowerLedger

open ArithmeticModel

private theorem sum_odd_Icc (a : ℕ) :
    (∑ r ∈ Finset.Icc 2 a, ((2 * r - 3 : ℕ) : ℝ)) =
      (((a - 1 : ℕ) : ℝ) ^ 2) := by
  induction a with
  | zero => simp
  | succ a ih =>
      by_cases ha : 1 ≤ a
      · rw [Finset.sum_Icc_succ_top (by omega), ih]
        have hodd : 2 * (a + 1) - 3 = 2 * a - 1 := by omega
        have h2a : 1 ≤ 2 * a := by omega
        rw [hodd, Nat.cast_sub h2a]
        norm_num [Nat.succ_eq_add_one, Nat.cast_sub ha]
        ring
      · have ha0 : a = 0 := by omega
        subst a
        norm_num

private theorem higherValuation_eq_cast_pred {p m : ℕ}
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

/-- The exact diagonal identity used in the proof of Lemma 7.5. -/
theorem higherValuation_sq_eq_weighted_sum_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m ^ 2 =
      ∑ r ∈ highExponents M,
        ((2 * r - 3 : ℕ) : ℝ) * divInd (p ^ r) m := by
  have hfacM : m.factorization p ≤ M := by
    exact (Nat.factorization_lt p hm.ne').le.trans hmM
  rw [higherValuation_eq_cast_pred hp hm]
  simp only [highExponents, divInd, hp.pow_dvd_iff_le_factorization hm.ne']
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 2 M).filter (fun r ↦ r ≤ m.factorization p) =
        Finset.Icc 2 (m.factorization p) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, sum_odd_Icc]





end Erdos390.Full.PowerLedger

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

theorem expect_zero (mu : FiniteProbability Omega) :
    mu.expect (fun _ ↦ 0) = 0 := by
  simp [expect]





























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



private theorem summable_quadraticHalfTerm : Summable quadraticHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hsq : Summable
      (fun i : ℕ ↦ (i : ℝ) ^ 2 * (1 / (2 : ℝ)) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable (fun i : ℕ ↦ (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two
  convert ((hsq.mul_left 2).add (hlin.mul_left 7)).add
    (hconst.mul_left 3) using 1
  funext i
  unfold quadraticHalfTerm
  push_cast
  ring



theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity

theorem sum_shifted_quadratic_half_le_mass (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
          (1 / (2 : ℝ)) ^ (r - 2)) ≤ quadraticHalfMass := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, quadraticHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hweight : 2 * r - 3 = 2 * (r - 2) + 1 := by omega
      have hshift : r + 1 = (r - 2) + 3 := by omega
      unfold quadraticHalfTerm g
      rw [hweight]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show (r : ℝ) + 1 = ((r - 2 : ℕ) : ℝ) + 3 by
        exact_mod_cast hshift]
    · exact hinj
  rw [heq, quadraticHalfMass]
  exact summable_quadraticHalfTerm.sum_le_tsum (s.image g)
    (fun i hi ↦ by unfold quadraticHalfTerm; positivity)

/-- The exact diagonal weight `(2r-3)` still aggregates on the
`p^{-2}` scale. -/
theorem sum_diagonalWeight_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
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
      have hweight0 : (0 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
      have hnum0 : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2))) ≤
            ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
              (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * quadraticHalfMass :=
      mul_le_mul_of_nonneg_left (sum_shifted_quadratic_half_le_mass R)
        (by positivity)
    _ = quadraticHalfMass / (p : ℝ) ^ 2 := by ring















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



private theorem sum_weighted_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A,
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m)) =
      ∑ k ∈ highExponents B,
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m) := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne', mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega



/-- Exact diagonal square ledger at the logarithmic cutoff. -/
theorem higherValuation_sq_eq_weighted_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m ^ 2 =
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m) := by
  rw [higherValuation_sq_eq_weighted_sum_of_le hp hm hmM]
  exact sum_weighted_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]

/-- Expectation commutes with an actual finite sum. -/
theorem expect_sum (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ i ∈ s, F i omega) =
      ∑ i ∈ s, mu.expect (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.expect_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.expect_add, ih]

end FiniteProbability

variable {Omega : Type*} [Fintype Omega] {M : ℕ}









/-- Pointwise diagonal square identity at the exact logarithmic cutoff. -/
theorem J_sq_eq_valuationCutoff_weighted_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    (fun omega ↦ law.J p omega ^ 2) = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) * law.Ip p k omega) := by
  funext omega
  exact higherValuation_sq_eq_weighted_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

/-- Expected diagonal square as the exact weighted prime-power sum. -/
theorem expect_J_sq_eq_valuationCutoff_weighted_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) =
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) *
          law.probability.expect (law.Ip p k)) := by
  rw [J_sq_eq_valuationCutoff_weighted_sum law hp,
    FiniteProbability.expect_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.expect_smul]

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



lemma pairAggregationConstant_nonneg : 0 ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  exact add_nonneg (by norm_num) quadraticHalfMass_nonneg

lemma eight_le_pairAggregationConstant : (8 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  nlinarith [quadraticHalfMass_nonneg]

lemma sixtyFour_le_pairAggregationConstant :
    (64 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  linarith [quadraticHalfMass_nonneg]

lemma quadraticHalfMass_le_pairAggregationConstant :
    quadraticHalfMass ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  norm_num

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)







/-- The exact diagonal square ledger contracts with its literal odd weight. -/
theorem expect_J_sq_le_of_cutoff_pointwise
    {p : ℕ} (hp : p.Prime) {K : ℝ} (hK : 0 ≤ K)
    (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        K * (((r : ℝ) + 1) / (p : ℝ) ^ r) + e r) :
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
      K * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          (((2 * r - 3 : ℕ) : ℝ) * e r) := by
  rw [expect_J_sq_eq_valuationCutoff_weighted_sum law hp]
  calc
    (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) *
          law.probability.expect (law.Ip p r))) ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          (((2 * r - 3 : ℕ) : ℝ) *
            (K * (((r : ℝ) + 1) / (p : ℝ) ^ r) + e r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hpoint r hr) (by positivity)
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) / (p : ℝ) ^ r))) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      calc
        _ = ∑ r ∈ highExponents (valuationCutoff p M),
              (K * (((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r)) +
                (((2 * r - 3 : ℕ) : ℝ) * e r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = (∑ r ∈ highExponents (valuationCutoff p M),
              K * (((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r))) +
              ∑ r ∈ highExponents (valuationCutoff p M),
                (((2 * r - 3 : ℕ) : ℝ) * e r) :=
          Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ K * (quadraticHalfMass / (p : ℝ) ^ 2) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      gcongr
      exact sum_diagonalWeight_raddone_inv_pow_le hp.two_le
    _ = K * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      ring



end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerSumAbsAggregation -/
section


/-!
# Sum-of-absolute-values prime-power aggregation

Paper Lemma 7.5 requires sums of absolute pointwise covariances.  These are
strictly stronger than the absolute value of the already-expanded `J`
covariance, so they are exported separately here.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerSumAbsAggregation

open ArithmeticModel
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff

noncomputable section

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)

/-- One-high aggregation with the sum of absolute covariances on the left. -/
theorem sum_abs_covJI_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq0 : 0 < q)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        K * (((r : ℝ) + 1) /
          ((p : ℝ) ^ r * (q : ℝ))) + e r) :
    (∑ r ∈ highExponents (valuationCutoff p M),
        |law.probability.covariance (law.Ip p r) (law.I q)|) ≤
      8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
        ∑ r ∈ highExponents (valuationCutoff p M), e r := by
  calc
    _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          (K * (((r : ℝ) + 1) /
            ((p : ℝ) ^ r * (q : ℝ))) + e r) := by
      exact Finset.sum_le_sum fun r hr ↦ hpoint r hr
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            ((r : ℝ) + 1) / (p : ℝ) ^ r) * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ K * (8 / (p : ℝ) ^ 2) * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      gcongr
      exact sum_raddone_inv_pow_le hp.two_le
    _ = _ := by ring

/-- Transposed one-high aggregation with the sum of absolute covariances. -/
theorem sum_abs_covIJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp0 : 0 < p) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        K * (((s : ℝ) + 1) /
          ((p : ℝ) * (q : ℝ) ^ s)) + e s) :
    (∑ s ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.I p) (law.Ip q s)|) ≤
      8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
        ∑ s ∈ highExponents (valuationCutoff q M), e s := by
  calc
    _ ≤ ∑ s ∈ highExponents (valuationCutoff q M),
          (K * (((s : ℝ) + 1) /
            ((p : ℝ) * (q : ℝ) ^ s)) + e s) := by
      exact Finset.sum_le_sum fun s hs ↦ hpoint s hs
    _ = K * (1 / (p : ℝ)) *
          (∑ s ∈ highExponents (valuationCutoff q M),
            ((s : ℝ) + 1) / (q : ℝ) ^ s) +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ K * (1 / (p : ℝ)) * (8 / (q : ℝ) ^ 2) +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      gcongr
      exact sum_raddone_inv_pow_le hq.two_le
    _ = _ := by ring

/-- Double-high aggregation with the literal double sum of absolute
covariances. -/
theorem sum_abs_covJJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) + e r s) :
    (∑ r ∈ highExponents (valuationCutoff p M),
      ∑ s ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.Ip p r) (law.Ip q s)|) ≤
      64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
  calc
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
        _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
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
      apply add_le_add _ le_rfl
      calc
        _ ≤ K * (8 / (p : ℝ) ^ 2) *
            (∑ s ∈ highExponents (valuationCutoff q M),
              ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsumP hK) hSQ0
        _ ≤ K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hsumQ (mul_nonneg hK hAP0)
    _ = _ := by ring

end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerSumAbsAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerGenericAggregation -/
section


/-!
# Generic finite aggregation for the five conclusions of Lemma 7.5

This module separates the finite prime-power summation from the source of
the pointwise estimates.  It can therefore be applied both to one
structured cell and to a tagged fixed finite mixture.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerGenericAggregation

open ArithmeticModel Scale
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerChamberError PaperPrimePowerPairAggregation
open PaperPrimePowerSumAbsAggregation PaperPrimePowerRow
open PaperPrimePowerLemma75 PaperValuationCutoff
open ValuationCutoff PrimeSums LocalFugacityBounds

noncomputable section



theorem genericAggregationRemainder_nonneg
    {E Tlin Tquad Tdiag Trow : ℝ} {n W : ℕ}
    (hE : 0 ≤ E) (hTlin : 0 ≤ Tlin) (hTquad : 0 ≤ Tquad)
    (hTdiag : 0 ≤ Tdiag) (hTrow : 0 ≤ Trow) :
    0 ≤ genericAggregationRemainder E Tlin Tquad Tdiag Trow n W := by
  unfold genericAggregationRemainder
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hpairE : 0 ≤ pairAggregationConstant * E :=
    mul_nonneg pairAggregationConstant_nonneg hE
  have hrowTerm : 0 ≤ pairAggregationConstant * E *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg hpairE (by linarith)) (by positivity)
  linarith

/-- Finite aggregation from four pointwise bounds and their residual
majorants.  The same remainder occurs in all five conclusions. -/
theorem primePowerTransferBounds_of_pointwise
    {Omega : Type*} [Fintype Omega] {M n W : ℕ}
    (law : BoundedValuationLaw Omega M)
    {Cmain E Tlin Tquad Tdiag Trow : ℝ}
    {eJI eIJ : ℕ → ℕ → ℕ → ℝ}
    {eJJ : ℕ → ℕ → ℕ → ℕ → ℝ}
    {eD : ℕ → ℕ → ℝ}
    (hn : 1 < n) (hW : 1 < W)
    (hCmain : 0 ≤ Cmain) (hE : 0 ≤ E)
    (hTlin : 0 ≤ Tlin) (hTquad : 0 ≤ Tquad)
    (hTdiag : 0 ≤ Tdiag) (hTrow : 0 ≤ Trow)
    (hJIpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        (Cmain * tPrime n p * tPrime n q + E) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) + eJI p q r)
    (hIJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        (Cmain * tPrime n p * tPrime n q + E) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) + eIJ p q s)
    (hJJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (Cmain * tPrime n p * tPrime n q + E) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) + eJJ p q r s)
    (hDpoint : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        (Cmain + E) * (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD p r)
    (htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M), eJI p q r) ≤
        Tlin * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)))
    (htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s) ≤
        Tlin * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2)
    (htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        ∑ s ∈ highExponents (valuationCutoff q M), eJJ p q r s) ≤
          Tquad * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2)
    (htailD : ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) * eD p r)) ≤
          Tdiag * (1 / (p : ℝ)) ^ 2)
    (htailRow : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            (((∑ r ∈ highExponents (valuationCutoff p M), eJI p q r)) +
              (∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s) +
              (∑ r ∈ highExponents (valuationCutoff p M),
                ∑ s ∈ highExponents (valuationCutoff q M), eJJ p q r s))) +
          3 * (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * eD p r))) ≤ Trow)
    (hbandT : bandTReciprocalSum n W ≤ 2 * Real.log 4) :
    PrimePowerTransferBounds law n W
      (pairAggregationConstant * Cmain * (2 * Real.log 4 + 5))
      (genericAggregationRemainder E Tlin Tquad Tdiag Trow n W) := by
  let Cpow := pairAggregationConstant * Cmain * (2 * Real.log 4 + 5)
  let R := genericAggregationRemainder E Tlin Tquad Tdiag Trow n W
  have hpairE : 0 ≤ pairAggregationConstant * E :=
    mul_nonneg pairAggregationConstant_nonneg hE
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hR : 0 ≤ R := genericAggregationRemainder_nonneg hE hTlin hTquad
    hTdiag hTrow
  have hCfactor : (1 : ℝ) ≤ 2 * Real.log 4 + 5 := by
    have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hCscale : pairAggregationConstant * Cmain ≤ Cpow := by
    dsimp only [Cpow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hCfactor
      (mul_nonneg pairAggregationConstant_nonneg hCmain)
  have hELinear : pairAggregationConstant * E + Tlin ≤ R := by
    dsimp only [R]
    unfold genericAggregationRemainder
    have hrowTerm : 0 ≤ pairAggregationConstant * E *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by positivity
    linarith
  have hEQuad : pairAggregationConstant * E + Tquad ≤ R := by
    dsimp only [R]
    unfold genericAggregationRemainder
    have hrowTerm : 0 ≤ pairAggregationConstant * E *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by positivity
    linarith
  have hEDiag : pairAggregationConstant * E + Tdiag ≤ R := by
    dsimp only [R]
    unfold genericAggregationRemainder
    have hrowTerm : 0 ≤ pairAggregationConstant * E *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by positivity
    linarith
  have hrow :=
    Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise
      law hn hW Cmain E Trow eJI eIJ eJJ eD hCmain hE
        hJIpoint hIJpoint hJJpoint hDpoint htailRow
  refine {
    ji := ?_
    ij := ?_
    jj := ?_
    diagonal := ?_
    row := ?_ }
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := Cmain * tPrime n p * tPrime n q + E
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg (mul_nonneg hCmain
          (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covJI_le_of_cutoff_pointwise
        law hp hq.pos hK₀ (eJI p q) (hJIpoint p hpBand q hqErase)
    have h8 : 8 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 (by positivity)) (by positivity))
      (htailJI p hpBand q hqBand))
    have hmainScaled := mul_le_mul_of_nonneg_right hCscale
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + Tlin ≤
        Cpow * tPrime n p * tPrime n q + R := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hELinear]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) +
          Tlin * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := hraw
      _ = (pairAggregationConstant * K₀ + Tlin) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := Cmain * tPrime n p * tPrime n q + E
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg (mul_nonneg hCmain
          (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covIJ_le_of_cutoff_pointwise
        law hp.pos hq hK₀ (eIJ p q) (hIJpoint p hpBand q hqErase)
    have h8 : 8 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 (by positivity)) (by positivity))
      (htailIJ p hpBand q hqBand))
    have hmainScaled := mul_le_mul_of_nonneg_right hCscale
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + Tlin ≤
        Cpow * tPrime n p * tPrime n q + R := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hELinear]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 +
          Tlin * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + Tlin) *
          (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := Cmain * tPrime n p * tPrime n q + E
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg (mul_nonneg hCmain
          (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covJJ_le_of_cutoff_pointwise
        law hp hq hK₀ (eJJ p q) (hJJpoint p hpBand q hqErase)
    have h64 : 64 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right sixtyFour_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h64 (by positivity)) (by positivity))
      (htailJJ p hpBand q hqBand))
    have hmainScaled := mul_le_mul_of_nonneg_right hCscale
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + Tquad ≤
        Cpow * tPrime n p * tPrime n q + R := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hEQuad]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) ^ 2 +
          Tquad * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + Tquad) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand
    have hp := prime_of_mem_primeBand hpBand
    let K₀ := Cmain + E
    have hK₀ : 0 ≤ K₀ := add_nonneg hCmain hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.expect_J_sq_le_of_cutoff_pointwise
        law hp hK₀ (eD p) (hDpoint p hpBand)
    have hquad : K₀ * quadraticHalfMass ≤ pairAggregationConstant * K₀ := by
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left
          quadraticHalfMass_le_pairAggregationConstant hK₀)
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right hquad (by positivity))
      (htailD p hpBand))
    have hcoef : pairAggregationConstant * K₀ + Tdiag ≤ Cpow + R := by
      dsimp only [K₀]
      nlinarith [hCscale, hEDiag]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 +
          Tdiag * (1 / (p : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + Tdiag) *
          (1 / (p : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand
    have hpRow := hrow p hpBand
    have hmainCoeff : 0 ≤ pairAggregationConstant * Cmain :=
      mul_nonneg pairAggregationConstant_nonneg hCmain
    have hfirst :
        (pairAggregationConstant * Cmain) *
            (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) ≤
          Cpow * (1 / (W : ℝ)) := by
      have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
      have hfactor : bandTReciprocalSum n W + 5 ≤
          2 * Real.log 4 + 5 := by linarith
      dsimp only [Cpow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hmainCoeff) hWinv
    have hrowError :
        pairAggregationConstant * E * (bandReciprocalSum n W + 5) *
              (1 / (W : ℝ)) + Trow ≤ R := by
      dsimp only [R]
      unfold genericAggregationRemainder
      linarith
    calc
      _ ≤ (pairAggregationConstant * Cmain) *
              (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) +
            pairAggregationConstant * E *
                (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) + Trow :=
        hpRow
      _ ≤ Cpow * (1 / (W : ℝ)) + R := by linarith

end

end Erdos390.Full.PaperPrimePowerGenericAggregation

end

universe u_1
theorem solution :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] {M n W : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M) {Cmain E Tlin Tquad Tdiag Trow : Real}
  {eJI eIJ : Nat → Nat → Nat → Real} {eJJ : Nat → Nat → Nat → Nat → Real} {eD : Nat → Nat → Real},
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      LE.le.{0} (0 : Real) Cmain →
        LE.le.{0} (0 : Real) E →
          LE.le.{0} (0 : Real) Tlin →
            LE.le.{0} (0 : Real) Tquad →
              LE.le.{0} (0 : Real) Tdiag →
                LE.le.{0} (0 : Real) Trow →
                  (∀ (p : Nat),
                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                        ∀ (q : Nat),
                          Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                            ∀ (r : Nat),
                              Membership.mem.{0, 0}
                                  (Erdos390.Full.ArithmeticModel.highExponents
                                    (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                                  r →
                                LE.le.{0}
                                  (abs.{0}
                                    (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.I.{u_1} law q)))
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} Cmain (Erdos390.Full.ArithmeticModel.tPrime n p))
                                          (Erdos390.Full.ArithmeticModel.tPrime n q))
                                        E)
                                      (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) ↑q)))
                                    (eJI p q r))) →
                    (∀ (p : Nat),
                        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                          ∀ (q : Nat),
                            Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                              ∀ (s : Nat),
                                Membership.mem.{0, 0}
                                    (Erdos390.Full.ArithmeticModel.highExponents
                                      (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                                    s →
                                  LE.le.{0}
                                    (abs.{0}
                                      (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.I.{u_1} law p)
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q s)))
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} Cmain (Erdos390.Full.ArithmeticModel.tPrime n p))
                                            (Erdos390.Full.ArithmeticModel.tPrime n q))
                                          E)
                                        (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real))
                                          (HMul.hMul.{0, 0, 0} (↑p) (HPow.hPow.{0, 0, 0} (↑q) s))))
                                      (eIJ p q s))) →
                      (∀ (p : Nat),
                          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                            ∀ (q : Nat),
                              Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p)
                                  q →
                                ∀ (r : Nat),
                                  Membership.mem.{0, 0}
                                      (Erdos390.Full.ArithmeticModel.highExponents
                                        (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                                      r →
                                    ∀ (s : Nat),
                                      Membership.mem.{0, 0}
                                          (Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                                          s →
                                        LE.le.{0}
                                          (abs.{0}
                                            (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1}
                                                law)
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q
                                                s)))
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} Cmain (Erdos390.Full.ArithmeticModel.tPrime n p))
                                                  (Erdos390.Full.ArithmeticModel.tPrime n q))
                                                E)
                                              (HDiv.hDiv.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                                  (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real)))
                                                (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r)
                                                  (HPow.hPow.{0, 0, 0} (↑q) s))))
                                            (eJJ p q r s))) →
                        (∀ (p : Nat),
                            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                              ∀ (r : Nat),
                                Membership.mem.{0, 0}
                                    (Erdos390.Full.ArithmeticModel.highExponents
                                      (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                                    r →
                                  LE.le.{0}
                                    (Erdos390.Full.FiniteProbability.expect.{u_1}
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r))
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} Cmain E)
                                        (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                          (HPow.hPow.{0, 0, 0} (↑p) r)))
                                      (eD p r))) →
                          (∀ (p : Nat),
                              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                ∀ (q : Nat),
                                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                    LE.le.{0}
                                      (∑
                                        r ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                        eJI p q r)
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0} Tlin
                                          (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                                        (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q))) →
                            (∀ (p : Nat),
                                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                  ∀ (q : Nat),
                                    Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                      LE.le.{0}
                                        (∑
                                          s ∈
                                            Erdos390.Full.ArithmeticModel.highExponents
                                              (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                          eIJ p q s)
                                        (HMul.hMul.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} Tlin (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                                          (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat)))) →
                              (∀ (p : Nat),
                                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                    ∀ (q : Nat),
                                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                        LE.le.{0}
                                          (∑
                                            r ∈
                                              Erdos390.Full.ArithmeticModel.highExponents
                                                (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                            ∑
                                              s ∈
                                                Erdos390.Full.ArithmeticModel.highExponents
                                                  (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                              eJJ p q r s)
                                          (HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} Tquad
                                              (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                                            (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat)))) →
                                (∀ (p : Nat),
                                    Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                      LE.le.{0}
                                        (∑
                                          r ∈
                                            Erdos390.Full.ArithmeticModel.highExponents
                                              (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                          HMul.hMul.{0, 0, 0}
                                            (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)))
                                            (eD p r))
                                        (HMul.hMul.{0, 0, 0} Tdiag
                                          (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))) →
                                  (∀ (p : Nat),
                                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                        LE.le.{0}
                                          (HMul.hMul.{0, 0, 0} (↑p)
                                            (HAdd.hAdd.{0, 0, 0}
                                              (∑ q ∈ Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p,
                                                HAdd.hAdd.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (∑
                                                      r ∈
                                                        Erdos390.Full.ArithmeticModel.highExponents
                                                          (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                      eJI p q r)
                                                    (∑
                                                      s ∈
                                                        Erdos390.Full.ArithmeticModel.highExponents
                                                          (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                                      eIJ p q s))
                                                  (∑
                                                    r ∈
                                                      Erdos390.Full.ArithmeticModel.highExponents
                                                        (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                    ∑
                                                      s ∈
                                                        Erdos390.Full.ArithmeticModel.highExponents
                                                          (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                                      eJJ p q r s))
                                              (HMul.hMul.{0, 0, 0} (3 : Real)
                                                (∑
                                                  r ∈
                                                    Erdos390.Full.ArithmeticModel.highExponents
                                                      (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                                  HMul.hMul.{0, 0, 0}
                                                    (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)))
                                                    (eD p r)))))
                                          Trow) →
                                    LE.le.{0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W)
                                        (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real))) →
                                      Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_1} law n W
                                        (HMul.hMul.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0}
                                            Erdos390.Full.PaperPrimePowerPairAggregation.pairAggregationConstant Cmain)
                                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real)))
                                            (5 : Real)))
                                        (Erdos390.Full.PaperPrimePowerGenericAggregation.genericAggregationRemainder E
                                          Tlin Tquad Tdiag Trow n W) := by
  exact @Erdos390.Full.PaperPrimePowerGenericAggregation.primePowerTransferBounds_of_pointwise
