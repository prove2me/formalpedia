-- Prove2me | solution 1 for Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_primePowerModuli_inv_lcm_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:52:33.638223+00:00
-- url     : https://prove2.me/submissions/6ffebbf0-a703-4c7b-91da-0df603f321c2

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PrimePowerTaylorLedger_sum_positiveExponents_pair_inv_lcm_le

/- Source module: Erdos390.Full.ValuationScoreDomination -/
section


open scoped BigOperators

namespace Erdos390.Full.ValuationScoreDomination

open ArithmeticModel DivisibilityMomentBounds

noncomputable section



theorem primePowerMap_injective {P : Finset ℕ} {M : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2)
      (↑(P ×ˢ positiveExponents M) : Set (ℕ × ℕ)) := by
  intro pk hpk ql hql heq
  have hpP := (Finset.mem_product.mp hpk).1
  have hkM := (Finset.mem_product.mp hpk).2
  have hqP := (Finset.mem_product.mp hql).1
  have hlM := (Finset.mem_product.mp hql).2
  have hk0 : pk.2 ≠ 0 := by
    rw [mem_positiveExponents] at hkM
    omega
  have hl0 : ql.2 ≠ 0 := by
    rw [mem_positiveExponents] at hlM
    omega
  have hinj := Nat.Prime.pow_inj' (hprime pk.1 hpP) (hprime ql.1 hqP)
    hk0 hl0 heq
  exact Prod.ext hinj.1 hinj.2













theorem sum_inv_primePowerModuli_eq
    (P : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M, 1 / ((p ^ k : ℕ) : ℝ) := by
  unfold primePowerModuli
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro a ha b hb hab
    exact primePowerMap_injective hprime ha hb hab

private theorem sum_Icc_half_pow_pred_eq (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 / (2 : ℝ)) ^ (k - 1)) =
      ∑ i ∈ Finset.range M, (1 / (2 : ℝ)) ^ i := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      simp

/-- The reciprocal mass of the positive powers of one prime is bounded by
the corresponding infinite geometric series. -/
theorem sum_inv_prime_powers_le (p M : ℕ) (hp2 : 2 ≤ p) :
    (∑ k ∈ positiveExponents M, 1 / ((p ^ k : ℕ) : ℝ)) ≤
      2 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    _ ≤ ∑ k ∈ positiveExponents M,
        (1 / (p : ℝ)) * (1 / (2 : ℝ)) ^ (k - 1) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [mem_positiveExponents] at hk
      have hpow : (2 : ℝ) ^ (k - 1) ≤ (p : ℝ) ^ (k - 1) := by gcongr
      have hpkpow : (p : ℝ) ^ k =
          (p : ℝ) * (p : ℝ) ^ (k - 1) := by
        calc
          (p : ℝ) ^ k = (p : ℝ) ^ ((k - 1) + 1) := by
            congr 1
            omega
          _ = (p : ℝ) * (p : ℝ) ^ (k - 1) := by
            rw [pow_succ']
      calc
        1 / ((p ^ k : ℕ) : ℝ) = 1 / ((p : ℝ) ^ k) := by norm_num
        _ = 1 / ((p : ℝ) * (p : ℝ) ^ (k - 1)) := by
          rw [hpkpow]
        _ ≤ 1 / ((p : ℝ) * (2 : ℝ) ^ (k - 1)) := by
          gcongr
        _ = (1 / (p : ℝ)) * (1 / (2 : ℝ)) ^ (k - 1) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ)) *
        (∑ k ∈ Finset.Icc 1 M, (1 / (2 : ℝ)) ^ (k - 1)) := by
      rw [Finset.mul_sum]
      rfl
    _ = (1 / (p : ℝ)) *
        (∑ i ∈ Finset.range M, (1 / (2 : ℝ)) ^ i) := by
      rw [sum_Icc_half_pow_pred_eq]
    _ ≤ (1 / (p : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by positivity)
    _ = 2 / (p : ℝ) := by ring

/-- The reciprocal mass of all relevant prime powers is at most twice the
reciprocal mass of the underlying primes.  The constant is independent of
the truncation endpoint `M`. -/
theorem sum_inv_primePowerModuli_le
    (P : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) ≤
      2 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [sum_inv_primePowerModuli_eq P M hprime]
  calc
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_inv_prime_powers_le p M (hprime p hp).two_le
    _ = 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end

end Erdos390.Full.ValuationScoreDomination

end

/- Source module: Erdos390.Full.PaperMediumNuisanceInputReduction -/
section


/-!
# Exact reductions for the two medium-law nuisance inputs

The nuisance Schur row in paper Lemma 8.6 uses two arithmetic facts about
the literal medium-prime component laws:

* a Stieltjes bound for `Cov(v_p, log (m / n))` inside one cell; and
* agreement, to reciprocal-logarithmic precision, of `E v_p` in two cells.

This file proves all finite probability, Abel summation, prime-power
summation, and physical-log identifications surrounding those two facts.
It intentionally does **not** replace the remaining arithmetic estimates by
a bundled certificate.  The hypotheses in the two terminal reductions are
the literal moving-prefix estimate and the literal prime-power/tail
estimates which still have to be obtained from the marked-cell theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.Full

noncomputable section

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

























































end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry













/-- One forced prime-valuation row against the complete prime-power score
has reciprocal scale `1/p`.  Distinct score primes give the product ledger;
the only non-coprime contribution is the already closed same-prime ledger. -/
theorem sum_positiveExponents_primePowerModuli_inv_lcm_le
    (P : Finset ℕ) (M p : ℕ) (hpP : p ∈ P)
    (hprime : ∀ q ∈ P, q.Prime) :
    (∑ r ∈ positiveExponents M,
        ∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm (p ^ r) a : ℝ)) ≤
      (4 * (∑ q ∈ P, 1 / (q : ℝ)) +
        positivePrimePowerLcmConstant) / (p : ℝ) := by
  have hp := hprime p hpP
  have hrewrite (r : ℕ) :
      (∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm (p ^ r) a : ℝ)) =
        ∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ) := by
    unfold primePowerModuli
    rw [Finset.sum_image]
    · rw [Finset.sum_product]
    · intro a ha b hb hab
      exact primePowerMap_injective hprime ha hb hab
  simp_rw [hrewrite]
  let Hp : ℝ := ∑ r ∈ positiveExponents M,
    1 / ((p ^ r : ℕ) : ℝ)
  let U : ℝ := ∑ q ∈ P, ∑ k ∈ positiveExponents M,
    1 / ((q ^ k : ℕ) : ℝ)
  let Qp : ℝ := ∑ r ∈ positiveExponents M,
    ∑ k ∈ positiveExponents M,
      1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
  have hterm (r : ℕ) (hr : r ∈ positiveExponents M) :
      (∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ)) ≤
        (∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
        ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ) := by
    have hq (q : ℕ) (hqP : q ∈ P) :
        (∑ k ∈ positiveExponents M,
            1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ)) ≤
          (∑ k ∈ positiveExponents M,
            1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
          if q = p then
            ∑ k ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
          else 0 := by
      by_cases hqp : q = p
      · subst q
        rw [if_pos rfl]
        exact le_add_of_nonneg_left (by positivity)
      · rw [if_neg hqp, add_zero]
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro k hk
        have hpq : Nat.Coprime p q :=
          (Nat.coprime_primes hp (hprime q hqP)).mpr (Ne.symm hqp)
        rw [((hpq.pow_left r).pow_right k).lcm_eq_mul]
    calc
      _ ≤ ∑ q ∈ P,
          ((∑ k ∈ positiveExponents M,
              1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
            if q = p then
              ∑ k ∈ positiveExponents M,
                1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
            else 0) := Finset.sum_le_sum fun q hqP ↦ hq q hqP
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [hpP]
  have hsum :
      (∑ r ∈ positiveExponents M,
        ∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ)) ≤ Hp * U + Qp := by
    calc
      _ ≤ ∑ r ∈ positiveExponents M,
          ((∑ q ∈ P, ∑ k ∈ positiveExponents M,
              1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
            ∑ k ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)) :=
        Finset.sum_le_sum fun r hr ↦ hterm r hr
      _ = Hp * U + Qp := by
        rw [Finset.sum_add_distrib]
        dsimp only [Hp, U, Qp]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        norm_num only [Nat.cast_mul]
        ring
  have hHp : Hp ≤ 2 / (p : ℝ) := by
    dsimp only [Hp]
    exact sum_inv_prime_powers_le p M hp.two_le
  have hU : U ≤ 2 * (∑ q ∈ P, 1 / (q : ℝ)) := by
    dsimp only [U]
    have hraw := sum_inv_primePowerModuli_le P M hprime
    rw [sum_inv_primePowerModuli_eq P M hprime] at hraw
    exact hraw
  have hQp : Qp ≤ positivePrimePowerLcmConstant / (p : ℝ) := by
    dsimp only [Qp]
    exact sum_positiveExponents_pair_inv_lcm_le hp
  have hHp0 : 0 ≤ Hp := by dsimp only [Hp]; positivity
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hT0 : 0 ≤ (∑ q ∈ P, 1 / (q : ℝ)) := by positivity
  calc
    _ ≤ Hp * U + Qp := hsum
    _ ≤ (2 / (p : ℝ)) *
          (2 * (∑ q ∈ P, 1 / (q : ℝ))) +
        positivePrimePowerLcmConstant / (p : ℝ) := by
      exact add_le_add (mul_le_mul hHp hU hU0 (by positivity)) hQp
    _ = (4 * (∑ q ∈ P, 1 / (q : ℝ)) +
        positivePrimePowerLcmConstant) / (p : ℝ) := by ring

end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]



















end FiniteProbability

namespace FiniteLogStieltjes

open Finset Set

variable {Omega : Type*} [Fintype Omega]





end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]





end GuardedUniformCell

namespace PrimePowerTail

open Finset

variable {Omega : Type*} [Fintype Omega]



end PrimePowerTail

namespace PaperBridgeFit

open ArithmeticBandGeometry FiniteLogStieltjes

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

theorem solution :
∀ (P : Finset.{0} Nat) (M p : Nat),
  Membership.mem.{0, 0} P p →
    (∀ (q : Nat), Membership.mem.{0, 0} P q → Nat.Prime q) →
      LE.le.{0}
        (∑ r ∈ Erdos390.Full.ArithmeticModel.positiveExponents M,
          ∑ a ∈ Erdos390.Full.ValuationScoreDomination.primePowerModuli P M,
            HDiv.hDiv.{0, 0, 0} (1 : Real) ↑(Nat.lcm (HPow.hPow.{0, 0, 0} p r) a))
        (HDiv.hDiv.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) (∑ q ∈ P, HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q))
            Erdos390.Full.PrimePowerTaylorLedger.positivePrimePowerLcmConstant)
          ↑p) := by
  exact @Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_primePowerModuli_inv_lcm_le
