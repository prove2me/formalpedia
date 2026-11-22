-- Prove2me | solution 1 for Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted.exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:17:44.397204+00:00
-- url     : https://prove2.me/submissions/281050ae-3204-4cc0-a2a5-144b24b00562

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Theorems.Thm_Erdos390_Full_PaperPrimePowerTailRow_eventually_tailRowMajorant_le_limit
import Theorems.Thm_Erdos390_Full_PaperRawPrefixValuationRow_exists_uniform_rawCell_valuation_prefix_bound_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_Full_PrimePowerTaylorLedger_sum_positiveExponents_primePowerModuli_inv_lcm_le


section
theorem Erdos390.Full.PaperRawPrefixValuationRow.exists_uniform_rawCell_valuation_prefix_bound : Erdos390.RemainingAnalyticGoal004_006 := @Erdos390.Full.PaperRawPrefixValuationRow.exists_uniform_rawCell_valuation_prefix_bound_compact
end
/- Source module: Erdos390.Full.FiniteTiltTV -/
section


/-!
# Total-variation control for finite exponential tilts

This supplies the normalization estimate used to compare each finite-`n`
tilted nuisance covariance with its own finite-`n` baseline.  The bound is
proved directly from the exponential density ratio.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]











theorem exponentialDeviation_nonneg (mu : FiniteProbability Omega)
    (S : Omega → ℝ) : 0 ≤ mu.exponentialDeviation S := by
  unfold exponentialDeviation expect
  exact Finset.sum_nonneg fun omega _ ↦
    mul_nonneg (mu.mass_nonneg omega) (abs_nonneg _)



theorem abs_expPartition_sub_one_le_deviation
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    |mu.expPartition S - 1| ≤ mu.exponentialDeviation S := by
  have hrewrite : mu.expPartition S - 1 =
      ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
    calc
      mu.expPartition S - 1 =
          (∑ omega, mu.mass omega * Real.exp (S omega)) -
            ∑ omega, mu.mass omega := by
              rw [expPartition, expect, mu.mass_sum]
      _ = ∑ omega,
          (mu.mass omega * Real.exp (S omega) - mu.mass omega) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
            apply Finset.sum_congr rfl
            intro omega _
            ring
  rw [hrewrite]
  calc
    |∑ omega, mu.mass omega * (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.exponentialDeviation S := by
      unfold exponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg omega)]

theorem expPartition_lower_bound
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    1 - mu.exponentialDeviation S ≤ mu.expPartition S := by
  have h := mu.abs_expPartition_sub_one_le_deviation S
  have hneg : -mu.exponentialDeviation S ≤
      -|mu.expPartition S - 1| := neg_le_neg h
  have habs : -|mu.expPartition S - 1| ≤
      mu.expPartition S - 1 := neg_abs_le _
  linarith





end FiniteProbability

end

end Erdos390.Full

end

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































end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

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

/-- A subset of positive integers up to `M` has at most `M / D` members
divisible by a modulus `D`. -/
theorem card_filter_dvd_le_div (S : Finset ℕ) {M D : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M) :
    (S.filter (D ∣ ·)).card ≤ M / D := by
  have hsubset : S.filter (D ∣ ·) ⊆
      (Finset.Ioc 0 M).filter (D ∣ ·) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨Finset.mem_Ioc.mpr ⟨hSpos m hm.1, hSle m hm.1⟩, hm.2⟩
  calc
    (S.filter (D ∣ ·)).card ≤
        ((Finset.Ioc 0 M).filter (D ∣ ·)).card :=
      Finset.card_le_card hsubset
    _ = M / D := Nat.Ioc_filter_dvd_card_eq_div M D

/-- A finite sum of an actual divisor indicator is the cardinality of the
corresponding filtered set. -/
theorem sum_divInd_eq_card_filter (S : Finset ℕ) (D : ℕ) :
    (∑ m ∈ S, divInd D m) = ((S.filter (D ∣ ·)).card : ℝ) := by
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [divInd]

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

/-- For coprime moduli, products of divisor indicators use the ordinary
product modulus. -/
theorem divInd_mul_eq_product_of_coprime {a b m : ℕ}
    (hcop : Nat.Coprime a b) :
    divInd a m * divInd b m = divInd (a * b) m := by
  rw [divInd_mul_eq_lcm, hcop.lcm_eq_mul]





private theorem sum_divInd_le_real_div (S : Finset ℕ) {M N : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M) :
    (∑ m ∈ S, divInd N m) ≤ (M : ℝ) / (N : ℝ) := by
  rw [sum_divInd_eq_card_filter]
  calc
    ((S.filter (N ∣ ·)).card : ℝ) ≤ ((M / N : ℕ) : ℝ) := by
      exact_mod_cast card_filter_dvd_le_div S hSpos hSle
    _ ≤ (M : ℝ) / (N : ℝ) := Nat.cast_div_le

/-- Exact first-moment multiple-counting bound.  The coprimality condition
is precisely the paper's omission of the forced local primes from the
global score. -/
theorem sum_marked_divisorScore_le (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    (∑ m ∈ S, divInd D m * divisorScore R m) ≤
      ((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) := by
  have hterm : ∀ a ∈ R,
      (∑ m ∈ S, divInd (D * a) m) ≤
        ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
    intro a ha
    calc
      (∑ m ∈ S, divInd (D * a) m) ≤
          (M : ℝ) / ((D * a : ℕ) : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
        have hD0 : (D : ℝ) ≠ 0 := by positivity
        have ha0 : (a : ℝ) ≠ 0 := by
          exact_mod_cast (hRpos a ha).ne'
        norm_num only [Nat.cast_mul]
        field_simp [hD0, ha0]
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) =
        ∑ a ∈ R, ∑ m ∈ S, divInd (D * a) m := by
      unfold divisorScore
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro m hm
      exact divInd_mul_eq_product_of_coprime (hcop a ha)
    _ ≤ ∑ a ∈ R,
        ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
      exact Finset.sum_le_sum fun a ha => hterm a ha
    _ = ((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) := by
      rw [Finset.mul_sum]



/-- Exact first marked moment without a coprimality assumption.  The price
for retaining a forced local prime in the score is the literal lcm ledger;
no product-denominator replacement is made. -/
theorem sum_marked_divisorScore_lcm_le (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a) :
    (∑ m ∈ S, divInd D m * divisorScore R m) ≤
      (M : ℝ) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
  have hterm : ∀ a ∈ R,
      (∑ m ∈ S, divInd (Nat.lcm D a) m) ≤
        (M : ℝ) * (1 / (Nat.lcm D a : ℝ)) := by
    intro a ha
    have hlcmPos : 0 < Nat.lcm D a := Nat.lcm_pos hD (hRpos a ha)
    calc
      (∑ m ∈ S, divInd (Nat.lcm D a) m) ≤
          (M : ℝ) / (Nat.lcm D a : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = (M : ℝ) * (1 / (Nat.lcm D a : ℝ)) := by ring
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) =
        ∑ a ∈ R, ∑ m ∈ S, divInd (Nat.lcm D a) m := by
      unfold divisorScore
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro m hm
      exact divInd_mul_eq_lcm D a m
    _ ≤ ∑ a ∈ R,
        (M : ℝ) * (1 / (Nat.lcm D a : ℝ)) := by
      exact Finset.sum_le_sum fun a ha ↦ hterm a ha
    _ = (M : ℝ) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
      rw [Finset.mul_sum]





private theorem endpoint_card_ratio_le {S : Finset ℕ} {M : ℕ} {c : ℝ}
    (hc : 0 < c) (hM : 0 < M)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ)) :
    (M : ℝ) / (S.card : ℝ) ≤ 1 / c := by
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hMle : (M : ℝ) ≤ (S.card : ℝ) / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using hcard)
  calc
    (M : ℝ) / (S.card : ℝ) ≤
        ((S.card : ℝ) / c) / (S.card : ℝ) :=
      div_le_div_of_nonneg_right hMle hcardPos.le
    _ = 1 / c := by field_simp [ne_of_gt hc, ne_of_gt hcardPos]

/-- Normalized first omitted-score moment.  A lower density bound for the
cell converts the exact endpoint count into the paper's `1/D` scale. -/
theorem uniformAverage_marked_divisorScore_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    uniformAverage S (fun m => divInd D m * divisorScore R m) ≤
      (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ) := by
  have hsum := sum_marked_divisorScore_le S R hD hSpos hSle hRpos hcop
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hrecipNonneg : 0 ≤ ∑ a ∈ R, 1 / (a : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    positivity
  have hfactor : 0 ≤ (1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) :=
    mul_nonneg (by positivity) hrecipNonneg
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) / (S.card : ℝ) ≤
        (((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) /
          (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ((1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) := by ring
    _ ≤ (1 / c) *
        ((1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_right hratio hfactor
    _ = (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ) := by ring



/-- Normalized literal-lcm first moment.  Unlike
`uniformAverage_marked_divisorScore_le`, this theorem also applies when the
score family contains the forced prime. -/
theorem uniformAverage_marked_divisorScore_lcm_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a) :
    uniformAverage S (fun m ↦ divInd D m * divisorScore R m) ≤
      (1 / c) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
  have hsum := sum_marked_divisorScore_lcm_le
    S R hD hSpos hSle hRpos
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hledger0 : 0 ≤
      ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    have hlcm : 0 < Nat.lcm D a := Nat.lcm_pos hD (hRpos a ha)
    positivity
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) / (S.card : ℝ) ≤
        ((M : ℝ) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ)) /
          (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by ring
    _ ≤ (1 / c) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hledger0



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











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

































/-! ## Normalization algebra -/







/-- The unmarked structured cell has a fixed positive linear density.  This
is the normalization lower bound used by all subsequent compact tilts. -/
theorem exists_structuredCell_density_lower_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      paperCellDensity P A B * (n : ℝ) / 2 ≤
        ((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) := by
  obtain ⟨K, hK, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (2 : ℝ) ≤ y n ∧ 2 * K / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
      hLTop.eventually (Filter.eventually_ge_atTop (2 * K / c))] with
      n hn hy hden
    exact ⟨hn, hy, hden⟩
  obtain ⟨Nlarge, hNlarge⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max Ncount Nlarge, ?_⟩
  intro n hN
  have hNc : Ncount ≤ n := by omega
  have hNl : Nlarge ≤ n := by omega
  obtain ⟨hn, hy, hden⟩ := hNlarge n hNl
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hyNat2 : 2 ≤ yNat n := Nat.le_floor hy
  have h1d4 : 1 ≤ yNat n ^ 4 := by
    exact pow_pos (by omega : 0 < yNat n) 4
  have hbase₀ := hcount (n := n) (d := 1) hNc (by omega) h1d4
    (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) - c * (n : ℝ)| ≤
        K * (n : ℝ) / L n := by
    simpa [c, markedCell] using hbase₀
  have hscale : 2 * K ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  have hKdiv : K / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have herr : K * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K * (n : ℝ) / L n = (K / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hlower := (abs_le.mp (hbase.trans herr)).1
  dsimp only [c] at hlower ⊢
  linarith



end

end Erdos390.Full.PaperScaleMarkedCell

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







theorem expect_mono (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (hFG : ∀ omega, F omega ≤ G omega) : mu.expect F ≤ mu.expect G := by
  unfold expect
  apply Finset.sum_le_sum
  intro omega _
  exact mul_le_mul_of_nonneg_left (hFG omega) (mu.mass_nonneg omega)





















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

/- Source module: Erdos390.Full.OmittedScoreTilt -/
section


/-!
# Normalized marked-event bounds under an omitted-score tilt

The four-mark step in Lemma 7.5 first omits the forced local primes from
the score, estimates a marked numerator, and then divides by the tilted
partition function.  This file proves that normalization step for an actual
finite probability law.  The result keeps the marked and unmarked
exponential deviations separate, so a `1 / D` marked moment is not replaced
by an unscaled total-variation error.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]



theorem markedExponentialDeviation_nonneg
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    0 ≤ mu.markedExponentialDeviation A S := by
  unfold markedExponentialDeviation
  exact mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA omega) (abs_nonneg _)

/-- Global real-exponential increment bound, with no smallness hypothesis. -/
theorem abs_exp_sub_one_le_exp_abs_mul_abs (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| * |x| := by
  by_cases hx : 0 ≤ x
  · have hexpOne : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hbase := Real.add_one_le_exp (-x)
    have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos x).le
    have hprod : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hprod] at hmul
    rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr hexpOne)]
    nlinarith [Real.exp_pos x]
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hexpOne : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hxneg.le
    have hlinear := Real.add_one_le_exp x
    have hone : 1 ≤ Real.exp (-x) := Real.one_le_exp (neg_nonneg.mpr hxneg.le)
    have hmul : -x ≤ Real.exp (-x) * (-x) := by
      simpa using
        (mul_le_mul_of_nonneg_right hone (neg_nonneg.mpr hxneg.le))
    rw [abs_of_neg hxneg, abs_of_nonpos (sub_nonpos.mpr hexpOne)]
    nlinarith

/-- A pointwise score bound converts the marked first absolute moment into
an exponential-deviation bound.  The constant may depend on the already
fixed score box, while the arithmetic mark remains visible. -/
theorem markedExponentialDeviation_le_exp_mul_expect_abs
    (mu : FiniteProbability Omega) (A S : Omega → ℝ) {K : ℝ}
    (hA : ∀ omega, 0 ≤ A omega)
    (hbound : ∀ omega, |S omega| ≤ K) :
    mu.markedExponentialDeviation A S ≤
      Real.exp K * mu.expect (fun omega ↦ A omega * |S omega|) := by
  unfold markedExponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  have hexp : Real.exp |S omega| ≤ Real.exp K :=
    Real.exp_le_exp.mpr (hbound omega)
  have hinc : |Real.exp (S omega) - 1| ≤
      Real.exp K * |S omega| := by
    exact (abs_exp_sub_one_le_exp_abs_mul_abs (S omega)).trans
      (mul_le_mul_of_nonneg_right hexp (abs_nonneg _))
  calc
    mu.mass omega * (A omega * |Real.exp (S omega) - 1|) ≤
        mu.mass omega * (A omega * (Real.exp K * |S omega|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinc (hA omega))
        (mu.mass_nonneg omega)
    _ = Real.exp K * (mu.mass omega * (A omega * |S omega|)) := by ring

theorem exponentialDeviation_le_exp_mul_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ) {K : ℝ}
    (hbound : ∀ omega, |S omega| ≤ K) :
    mu.exponentialDeviation S ≤
      Real.exp K * mu.expect (fun omega ↦ |S omega|) := by
  have hmarked := mu.markedExponentialDeviation_le_exp_mul_expect_abs
    (fun _ ↦ (1 : ℝ)) S (fun _ ↦ zero_le_one) hbound
  simpa [markedExponentialDeviation] using hmarked





/-- The marked numerator differs from its untilted value by at most the
marked exponential deviation. -/
theorem abs_expWeighted_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    |mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
        mu.expect A| ≤ mu.markedExponentialDeviation A S := by
  have hrearrange :
      mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
          mu.expect A =
        ∑ omega, mu.mass omega * A omega *
          (Real.exp (S omega) - 1) := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  rw [hrearrange]
  calc
    |∑ omega, mu.mass omega * A omega *
        (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * A omega *
          (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.markedExponentialDeviation A S := by
      unfold markedExponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_mul, abs_of_nonneg (mu.mass_nonneg omega),
        abs_of_nonneg (hA omega)]
      ring







end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.UniformFiniteProbability -/
section


/-!
# Uniform probability on an actual finite cell

This is the exact bridge between counting averages on a finite arithmetic
cell and the `FiniteProbability` objects used by the tilt and covariance
modules.  Nonemptiness is explicit, so normalization never divides by a
silently vanishing cell cardinality.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Alpha : Type*}





/-- Expectation under the uniform law is the literal subtype sum divided by
the actual cell cardinality. -/
theorem uniformOnFinset_expect_eq (S : Finset Alpha) (hS : S.Nonempty)
    (F : S → ℝ) :
    (uniformOnFinset S hS).expect F =
      (∑ x : S, F x) / (S.card : ℝ) := by
  unfold expect
  calc
    (∑ x : S, (1 / (S.card : ℝ)) * F x) =
        (1 / (S.card : ℝ)) * ∑ x : S, F x := by
      rw [Finset.mul_sum]
    _ = (∑ x : S, F x) / (S.card : ℝ) := by ring

/-- Subtype summation is exactly the usual filtered finset summation. -/
theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

/-- Expectation written with the ambient function and the literal cell
cardinality. -/
theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.OmittedScoreCell -/
section


/-!
# Omitted-score normalization on an actual arithmetic cell

This module composes the genuine uniform probability law of a finite cell
with the marked exponential-tilt inequality.  All expectations in the result
are literal counting averages over that same cell; there is no implicit
identification between a counting formula and an abstract probability law.
-/

namespace Erdos390.Full.OmittedScoreCell

open FiniteProbability DivisibilityMomentBounds

noncomputable section

/-- Counting average on a nonempty finite cell is exactly expectation under
its genuine uniform finite probability law. -/
theorem uniform_expect_eq_uniformAverage
    (S : Finset ℕ) (hS : S.Nonempty) (F : ℕ → ℝ) :
    (uniformOnFinset S hS).expect (fun m : S ↦ F m) =
      uniformAverage S F := by
  rw [uniformOnFinset_expect_ambient_eq]
  rfl









end

end Erdos390.Full.OmittedScoreCell

end

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

/-- Deduplication loses no term: distinct positive powers of primes are
distinct moduli. -/
theorem divisorScore_primePowerModuli_eq
    (P : Finset ℕ) (M m : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    divisorScore (primePowerModuli P M) m =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  unfold divisorScore primePowerModuli
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro a ha b hb hab
    exact primePowerMap_injective hprime ha hb hab



theorem valuationScore_eq_indicator_sum_of_le
    (P : Finset ℕ) (eta : ℕ → ℝ) (L : ℝ) {m M : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuationScore P eta L m =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (eta p / L) * divInd (p ^ k) m := by
  unfold valuationScore
  apply Finset.sum_congr rfl
  intro p hp
  rw [valuation_eq_sum_divInd_of_le (hprime p hp) hm hmM,
    Finset.mul_sum]

/-- Box-uniform pointwise domination of the true valuation score by the
prime-power divisor score.  The coefficient `B/L` is independent of the
forced marked modulus. -/
theorem abs_valuationScore_le_divisorScore
    (P : Finset ℕ) (eta : ℕ → ℝ) {B L : ℝ} {m M : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hm : 0 < m) (hmM : m ≤ M)
    (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * divisorScore (primePowerModuli P M) m := by
  rw [valuationScore_eq_indicator_sum_of_le P eta L hprime hm hmM]
  calc
    _ ≤ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        |(eta p / L) * divInd (p ^ k) m| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun p hp ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (|eta p| / L) * divInd (p ^ k) m := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (divInd_nonneg (p ^ k) m)]
    _ ≤ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (B / L) * divInd (p ^ k) m := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (divInd_nonneg (p ^ k) m)
    _ = (B / L) *
        (∑ p ∈ P, ∑ k ∈ positiveExponents M, divInd (p ^ k) m) := by
      simp only [Finset.mul_sum]
    _ = (B / L) * divisorScore (primePowerModuli P M) m := by
      rw [divisorScore_primePowerModuli_eq P M m hprime]

theorem pos_of_mem_primePowerModuli {P : Finset ℕ} {M a : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : a ∈ primePowerModuli P M) : 0 < a := by
  rw [primePowerModuli, Finset.mem_image] at ha
  obtain ⟨pk, hpk, rfl⟩ := ha
  exact pow_pos (hprime pk.1 (Finset.mem_product.mp hpk).1).pos _



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

/- Source module: Erdos390.Full.ValuationTiltCell -/
section


/-!
# Actual compact valuation tilts on a finite cell

This file substitutes the genuine valuation score into the omitted-score
comparison.  Both divisor-score moments are discharged by exact
common-multiple counting; no probabilistic independence is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.ValuationTiltCell

open ArithmeticModel DivisibilityMomentBounds FiniteProbability
open OmittedScoreCell ValuationScoreDomination

noncomputable section





/-- Uniform bound for the genuine compact valuation score using the physical
logarithm rather than the (much larger) number of prime-power columns. -/
theorem abs_valuationScore_le_log_ratio
    (P : Finset ℕ) (eta : ℕ → ℝ) {m M W : ℕ} {B L : ℝ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hW : 1 < W) (hpW : ∀ p ∈ P, W ≤ p)
    (hB : 0 ≤ B) (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := by
  unfold valuationScore
  calc
    |∑ p ∈ P, (eta p / L) * valuation p m| ≤
        ∑ p ∈ P, |(eta p / L) * valuation p m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ P, (|eta p| / L) * valuation p m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (valuation_nonneg p m)]
    _ ≤ ∑ p ∈ P, (B / L) * valuation p m := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (valuation_nonneg p m)
    _ = (B / L) * (∑ p ∈ P, valuation p m) := by
      rw [Finset.mul_sum]
    _ ≤ (B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_valuation_le_log_ratio P hm hmM hW hpW)
        (div_nonneg hB hL.le)



end

end Erdos390.Full.ValuationTiltCell

end

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale



















private theorem primeBand_subset_primesUpTo (n W : ℕ) :
    primeBand n W ⊆ primesUpTo (yNat n) := by
  intro p hp
  have h := mem_primeBand.mp hp
  simp [primesUpTo, h.1, h.2.2]

















private theorem integral_one_div_mul_log {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, 1 / (t * Real.log t)) =
      Real.log (Real.log Y) - Real.log (Real.log 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume 2 Y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog0))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  rw [Set.uIcc_of_le hY] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog0 : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have hd := (Real.hasDerivAt_log ht0).log hlog0
  convert hd using 1
  field_simp

/-- An explicit Mertens-type upper bound, obtained from the global Chebyshev
bound by Abel summation.  It is sufficient for every harmonic loss in
Lemma 7.5 and does not invoke the prime number theorem as an assumption. -/
theorem fullReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullReciprocalSum Y ≤
      2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
  rw [fullReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogYhalf : (1 / 2 : ℝ) ≤ Real.log (Y : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) hYR
    nlinarith [Real.log_two_gt_d9]
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hboundary :
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
        2 * Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
          (Real.log 4 * (Y : ℝ)) /
            ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 2 * Real.log 4 := by
        field_simp [hY0.ne', hlogY0.ne']
        nlinarith
  have hint :
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
        3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
          ∫ t in (2 : ℝ)..Y,
            3 * Real.log 4 * (1 / (t * Real.log t)) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_mertensIntegrand hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have hlog0 : Real.log t ≠ 0 :=
            Real.log_ne_zero_of_pos_of_ne_one
              (by linarith [ht.1]) (by linarith [ht.1])
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (continuousAt_const.div
                (continuousAt_id.mul (Real.continuousAt_log ht0))
                (mul_ne_zero ht0 hlog0)))
        · intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
            have hmono : Real.log 2 ≤ Real.log t :=
              Real.log_le_log (by norm_num) ht.1
            nlinarith [Real.log_two_gt_d9]
          calc
            Chebyshev.theta t * (Real.log t + 1) /
                (t ^ 2 * Real.log t ^ 2) ≤
                (Real.log 4 * t) * (Real.log t + 1) /
                  (t ^ 2 * Real.log t ^ 2) := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
            _ ≤ 3 * Real.log 4 * (1 / (t * Real.log t)) := by
              field_simp [ht0.ne', (show Real.log t ≠ 0 by linarith)]
              nlinarith
      _ = 3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_mul_log hYR]
  linarith





theorem bandReciprocalSum_le_full (n W : ℕ) :
    bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  positivity

/-- The unweighted prime harmonic mass has precisely the `O(log L)` loss
allowed in Lemma 7.5.  The constant is explicit and independent of `W` and of
every later tilt box. -/
theorem eventually_bandReciprocalSum_le_logL (W : ℕ) :
    ∀ᶠ n in atTop,
      bandReciprocalSum n W ≤ 12 * Real.log (L n) := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLTop : Tendsto (fun n : ℕ => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hlog4nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4upper : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvLog2 : (Real.log 2)⁻¹ ≤ 2 := by
    rw [← one_div, one_div_le hlog2pos (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hloglog2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    calc
      (-1 : ℝ) ≤ 1 - (Real.log 2)⁻¹ := by linarith
      _ ≤ Real.log (Real.log 2) := Real.one_sub_inv_le_log_of_pos hlog2pos
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogLTop.eventually (eventually_ge_atTop (5 : ℝ))] with n hn hyn hLn hlogLn
  have hyNat : 2 ≤ yNat n := Nat.le_floor hyn
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hlogNatPos : 0 < Real.log (yNat n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogNatLeY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogNatLeL : Real.log (yNat n : ℝ) ≤ L n := by
    calc
      Real.log (yNat n : ℝ) ≤ Real.log (y n) := hlogNatLeY
      _ = (2 / 9 : ℝ) * L n := log_y hn
      _ ≤ L n := by nlinarith
  have hloglogNatLeL :
      Real.log (Real.log (yNat n : ℝ)) ≤ Real.log (L n) :=
    Real.log_le_log hlogNatPos hlogNatLeL
  have hraw :
      bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
    calc
      bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) :=
        bandReciprocalSum_le_full n W
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (Real.log (yNat n : ℝ)) - Real.log (Real.log 2)) :=
        fullReciprocalSum_le (yNat n) hyNat
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
        gcongr
  calc
    bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := hraw
    _ = Real.log 4 *
        (2 + 3 * Real.log (L n) - 3 * Real.log (Real.log 2)) := by ring
    _ ≤ Real.log 4 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_left _ hlog4nonneg
      nlinarith
    _ ≤ 3 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_right hlog4upper
      nlinarith
    _ ≤ 12 * Real.log (L n) := by nlinarith





end Erdos390.Full.PrimeSums

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























theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity



















end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Full.OmittedTiltFallback -/
section


/-!
# Arbitrary-modulus fallback under an omitted valuation tilt

The four-mark theorem gives the sharp Dickman main term.  Terms outside that
chamber only require an upper bound.  This file proves the required fallback
directly: a bounded exponential tilt changes every nonnegative event by at
most its pointwise density-ratio bound, and elementary multiple counting on
an actual positive cell gives the reciprocal divisor scale for every modulus.
-/

namespace Erdos390.Full

open ArithmeticModel DivisibilityMomentBounds

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]





end FiniteProbability

namespace OmittedTiltFallback

open FiniteProbability ValuationScoreDomination ValuationTiltCell

/-- Pure multiple counting: every divisor event on a positive cell of
density at least `c` has probability at most `1/(cD)`. -/
theorem uniformAverage_divInd_le
    (S : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    uniformAverage S (divInd D) ≤ 1 / (c * (D : ℝ)) := by
  have h := uniformAverage_marked_divisorScore_le S {1}
    hD hM hc hcard hSpos hSle
    (fun a ha ↦ by simp at ha; omega)
    (fun a ha ↦ by simp at ha; subst a; simp)
  have hone (m : ℕ) : divisorScore {1} m = 1 := by
    unfold divisorScore
    simp only [Finset.sum_singleton]
    simp [divInd]
  have hleft : (fun m ↦ divInd D m * divisorScore {1} m) = divInd D := by
    funext m
    rw [hone]
    ring
  rw [hleft] at h
  have hsum : (∑ a ∈ ({1} : Finset ℕ), 1 / (a : ℝ)) = 1 := by
    norm_num
  rw [hsum, mul_one] at h
  exact h



end OmittedTiltFallback

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.FullTiltPairChamber -/
section


/-!
# Full valuation tilt in the two-prime four-mark chamber

This is the paper-facing closure of the two-local restoration.  It combines

* the actual structured-cell omitted-score four-mark estimate,
* the exact `N_{r,s}/N_{0,0}` restoration identity,
* the arbitrary-modulus reciprocal fallback for every restoration term, and
* the uniform lower bound for the exact normalizer.

The conclusion concerns the genuine full valuation tilt over the genuine
structured cell.  No covariance estimate or analytic transfer is assumed.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPairChamber

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination ValuationCutoff
open PaperScaleMarkedCell OmittedTiltPairChamber OmittedTiltFallback
open TwoLocalRestoration TwoLocalPairRestoration
open TwoLocalRestorationBound PaperTwoLocalRestorationBound

noncomputable section





/-- The fallback density is positive for every positive physical upper
endpoint; the normalization `1 ≤ C` used by older wrappers is unnecessary. -/
theorem pairFallbackDensity_pos_of_pos (H : Pattern) {A C : ℝ}
    (hAC : A < C) (hC : 0 < C) :
    0 < pairFallbackDensity H A C := by
  unfold pairFallbackDensity
  exact div_pos (paperCellDensity_pos H hAC) (mul_pos (by norm_num) hC)









end

end Erdos390.Full.FullTiltPairChamber

end

/- Source module: Erdos390.Full.PaperPrimePowerTailLedger -/
section


/-!
# Actual prime-power tail and endpoint ledgers

This module closes the finite arithmetic part of the beyond-four-mark
argument in paper Lemma 7.5.  The exponent sets are the actual logarithmic
valuation cutoffs, the primes belong to the actual finite band cut off by
`yNat`, and the four-mark boundary is the literal integer inequality
`yNat n ^ 4 < D`.  No asymptotic `O` notation is used in the statements.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailLedger

open ArithmeticModel Scale ValuationCutoff PaperValuationCutoff

noncomputable section













































/-! ## Literal endpoint multiplicities -/







/-! ## Actual logarithmic cutoffs and paper-scale ledgers -/





lemma cutoffScale_pos {W : ℕ} (hW : 1 < W) : 0 < cutoffScale W := by
  unfold cutoffScale
  exact div_pos (by norm_num) (Real.log_pos (by exact_mod_cast hW))



















end

end Erdos390.Full.PaperPrimePowerTailLedger

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













end

end Erdos390.Full.PrimePowerCutoffCovariance

end

/- Source module: Erdos390.Full.PaperPrimePowerTailRow -/
section


/-!
# The literal beyond-four residual row

The residual functions of the four pointwise displays are exactly supported
on the finite beyond-four exponent sets.  This file identifies those sums
and applies the previously proved actual-cutoff tail ledgers.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailRow

open ArithmeticModel Scale ValuationCutoff
open OmittedTiltPairChamber
open PaperPrimePowerTailLedger PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays
open PrimeSums

noncomputable section

















/-! ## One row majorant -/



theorem tailRowMajorant_nonneg {G : ℝ} (hG : 0 ≤ G) {W n : ℕ}
    (hW : 1 < W) (hn : 1 < n) :
    0 ≤ tailRowMajorant G W n := by
  unfold tailRowMajorant
  dsimp only
  have hT : 0 ≤ G + G ^ 2 := by nlinarith [sq_nonneg G]
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hK : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hY : 0 ≤ (yNat n : ℝ) := by positivity
  have hYpow : 0 ≤ (yNat n : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hY _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hT (mul_nonneg (div_nonneg hK hY)
        (by linarith)))
      (mul_nonneg hT (div_nonneg (sq_nonneg _) hYpow)))
    (mul_nonneg (mul_nonneg (by norm_num) hG)
      (div_nonneg (sq_nonneg _) (sq_nonneg _)))





/-! ## Vanishing of the row majorant -/











/-- The polynomial tail remains negligible after the one harmonic
`log (L n)` loss used by the moving low band. -/
private theorem tendsto_L_sq_div_nat_rpow_mul_logL_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n)) atTop (nhds 0) := by
  have hcube : Tendsto (fun n : ℕ ↦
      L n ^ 3 / (n : ℝ) ^ a) atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : ℝ ↦ Real.log x ^ (3 : ℝ) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (3 : ℝ) / (n : ℝ) ^ a)
        atTop (nhds 0) at hnat
    simpa [L, Real.rpow_natCast] using hnat
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL1
    exact mul_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (Real.log_nonneg hL1)
  have hupper : ∀ᶠ n : ℕ in atTop,
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) ≤
        L n ^ 3 / (n : ℝ) ^ a := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL1
    have hL0 : 0 ≤ L n := zero_le_one.trans hL1
    have hlog0 : 0 ≤ Real.log (L n) := Real.log_nonneg hL1
    have hlogLe : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hL1)).trans (by linarith)
    have hden : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) _
    calc
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) =
          (L n ^ 2 * Real.log (L n)) / (n : ℝ) ^ a := by ring
      _ ≤ (L n ^ 2 * L n) / (n : ℝ) ^ a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogLe (sq_nonneg _)) hden
      _ = L n ^ 3 / (n : ℝ) ^ a := by ring
  exact squeeze_zero' hlower hupper hcube

/-- `tailRowMajorant` has the sharp rate required to divide by the moving
low-cell scale `alpha_0 \asymp 1 / log L`. -/
theorem tendsto_tailRowMajorant_mul_logL_zero
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      tailRowMajorant G W n * Real.log (L n)) atTop (nhds 0) := by
  have h1 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 1 / 5 by norm_num)
  have h2 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 2 / 15 by norm_num)
  have h3 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 2 / 5 by norm_num)
  have hlimitRate : Tendsto (fun n : ℕ ↦
      tailRowLimitMajorant G W n * Real.log (L n)) atTop (nhds 0) := by
    have ht1 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 13 * (G + G ^ 2) * cutoffScale W) atTop
      (nhds (13 * (G + G ^ 2) * cutoffScale W))).mul h1
    have ht2 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ (G + G ^ 2) * cutoffScale W ^ 2) atTop
      (nhds ((G + G ^ 2) * cutoffScale W ^ 2))).mul h2
    have ht3 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 6 * G * cutoffScale W ^ 2) atTop
      (nhds (6 * G * cutoffScale W ^ 2))).mul h3
    have hsum := (ht1.add ht2).add ht3
    have hsum0 : Tendsto (fun n : ℕ ↦
        (13 * (G + G ^ 2) * cutoffScale W) *
            ((L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) * Real.log (L n)) +
        ((G + G ^ 2) * cutoffScale W ^ 2) *
            ((L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) * Real.log (L n)) +
        (6 * G * cutoffScale W ^ 2) *
            ((L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ)) * Real.log (L n)))
        atTop (nhds 0) := by simpa only [mul_zero, add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold tailRowLimitMajorant
    ring
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ tailRowMajorant G W n * Real.log (L n) := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hL1
    exact mul_nonneg (tailRowMajorant_nonneg hG hW hn)
      (Real.log_nonneg hL1)
  have hupper : ∀ᶠ n : ℕ in atTop,
      tailRowMajorant G W n * Real.log (L n) ≤
        tailRowLimitMajorant G W n * Real.log (L n) := by
    filter_upwards [eventually_tailRowMajorant_le_limit G W hG hW,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hrow hL1
    exact mul_le_mul_of_nonneg_right hrow (Real.log_nonneg hL1)
  exact squeeze_zero' hlower hupper hlimitRate

end

end Erdos390.Full.PaperPrimePowerTailRow

end

/- Source module: Erdos390.Full.LocalizedMarkedTiltCovariance -/
section


/-!
# Localized covariance stability under a small exponential tilt

The physical/head residual in the paper is a second, small tilt of each
medium-prime cell law.  A total-variation estimate would lose the divisibility
mark.  This file instead keeps the marginal and joint-event scales visible.

Everything below is an exact statement about finite probability laws.  The
arithmetic application supplies reciprocal bounds for the three marked
events `A`, `B`, and `A * B`.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]









/-- Pure covariance algebra: three localized expectation perturbation bounds
give a localized covariance perturbation bound.  The product term is kept at
the product of the two marginal scales. -/
theorem abs_covariance_sub_covariance_le_of_expectation_perturbations
    (mu nu : FiniteProbability Omega) (A B : Omega → ℝ)
    {a b dA dB dAB : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (ha : mu.expect A ≤ a)
    (hb : mu.expect B ≤ b)
    (hdA0 : 0 ≤ dA)
    (hAperturb : |nu.expect A - mu.expect A| ≤ dA)
    (hBperturb : |nu.expect B - mu.expect B| ≤ dB)
    (hABperturb :
      |nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)| ≤ dAB) :
    |nu.covariance A B - mu.covariance A B| ≤
      dAB + (a + dA) * dB + b * dA := by
  have hmuA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hmuB0 : 0 ≤ mu.expect B := mu.expect_nonneg B hB0
  have ha0 : 0 ≤ a := hmuA0.trans ha
  have hb0 : 0 ≤ b := hmuB0.trans hb
  have hnuA : nu.expect A ≤ a + dA := by
    have hle : nu.expect A - mu.expect A ≤ dA :=
      (le_abs_self _).trans hAperturb
    linarith
  have hnuA0 : 0 ≤ nu.expect A := nu.expect_nonneg A hA0
  have hproduct :
      |nu.expect A * nu.expect B - mu.expect A * mu.expect B| ≤
        (a + dA) * dB + b * dA := by
    rw [show nu.expect A * nu.expect B - mu.expect A * mu.expect B =
        nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A) by ring]
    calc
      |nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A)| ≤
          |nu.expect A * (nu.expect B - mu.expect B)| +
            |mu.expect B * (nu.expect A - mu.expect A)| := abs_add_le _ _
      _ = nu.expect A * |nu.expect B - mu.expect B| +
            mu.expect B * |nu.expect A - mu.expect A| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnuA0, abs_of_nonneg hmuB0]
      _ ≤ (a + dA) * dB + b * dA :=
        add_le_add
          (mul_le_mul hnuA hBperturb (abs_nonneg _) (add_nonneg ha0 hdA0))
          (mul_le_mul hb hAperturb (abs_nonneg _) hb0)
  unfold covariance
  rw [show
      (nu.expect (fun omega ↦ A omega * B omega) -
            nu.expect A * nu.expect B) -
          (mu.expect (fun omega ↦ A omega * B omega) -
            mu.expect A * mu.expect B) =
        (nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B) by ring]
  have habs :
      |(nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| :=
    abs_sub _ _
  calc
    |(nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)) -
        (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| := habs
    _ ≤ dAB + ((a + dA) * dB + b * dA) :=
      add_le_add hABperturb hproduct
    _ = dAB + (a + dA) * dB + b * dA := by ring







end FiniteProbability

end

end Erdos390.Full

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



















































/-- First-moment counterpart of the literal-lcm Taylor ledger. -/
theorem uniformOnFinset_expect_abs_divInd_mul_abs_valuationScore_lcm_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (heta : ∀ p ∈ P, |eta p| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * ((1 / c) *
        ∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm D a : ℝ)) := by
  let R := primePowerModuli P M
  let beta : ℝ := B / L
  have hbeta : 0 ≤ beta := div_nonneg hB hL.le
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa only [R] using ha)
  have hpoint : ∀ m : S,
      |divInd D (m : ℕ)| * |valuationScore P eta L (m : ℕ)| ≤
        beta * (divInd D (m : ℕ) * divisorScore R (m : ℕ)) := by
    intro m
    have hscore := abs_valuationScore_le_divisorScore P eta hprime
      (hSpos m m.property) (hSle m m.property) hL heta
    have hdiv0 : 0 ≤ divInd D (m : ℕ) := divInd_nonneg _ _
    rw [abs_of_nonneg hdiv0]
    calc
      divInd D (m : ℕ) * |valuationScore P eta L (m : ℕ)| ≤
          divInd D (m : ℕ) *
            (beta * divisorScore R (m : ℕ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [beta, R] using hscore) hdiv0
      _ = beta *
          (divInd D (m : ℕ) * divisorScore R (m : ℕ)) := by ring
  have havg :=
    DivisibilityMomentBounds.uniformAverage_marked_divisorScore_lcm_le
      S R hD hM hc hcard hSpos hSle hRpos
  calc
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (uniformOnFinset S hS).expect (fun m : S ↦ beta *
        (divInd D (m : ℕ) * divisorScore R (m : ℕ))) :=
      (uniformOnFinset S hS).expect_mono _ _ hpoint
    _ = beta * DivisibilityMomentBounds.uniformAverage S
        (fun m ↦ divInd D m * divisorScore R m) := by
      rw [(uniformOnFinset S hS).expect_smul]
      congr 1
      exact Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage
        S hS (fun m ↦ divInd D m * divisorScore R m)
    _ ≤ beta * ((1 / c) *
        ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ)) :=
      mul_le_mul_of_nonneg_left havg hbeta
    _ = (B / L) * ((1 / c) *
        ∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm D a : ℝ)) := by
      rfl

/-- Summed local-valuation first Taylor moment.  The complete local-prime
dependence is exposed by the finite two-way lcm ledger. -/
theorem uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M p : ℕ} {B L c : ℝ}
    (hp : p.Prime) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuation p (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by
  let mu := uniformOnFinset S hS
  let score : S → ℝ := fun m ↦ valuationScore P eta L (m : ℕ)
  have hpoint : (fun m : S ↦ |valuation p (m : ℕ)| * |score m|) =
      fun m : S ↦ ∑ r ∈ positiveExponents M,
        |divInd (p ^ r) (m : ℕ)| * |score m| := by
    funext m
    rw [abs_of_nonneg (valuation_nonneg p (m : ℕ)),
      valuation_eq_sum_divInd_of_le hp (hSpos m m.property)
        (hSle m m.property)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [abs_of_nonneg (divInd_nonneg (p ^ r) (m : ℕ))]
  have hexpand : mu.expect (fun m : S ↦
      ∑ r ∈ positiveExponents M,
        |divInd (p ^ r) (m : ℕ)| * |score m|) =
      ∑ r ∈ positiveExponents M, mu.expect (fun m : S ↦
        |divInd (p ^ r) (m : ℕ)| * |score m|) := by
    exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
      (positiveExponents M)
      (fun r m ↦ |divInd (p ^ r) (m : ℕ)| * |score m|)
  rw [hpoint, hexpand]
  calc
    (∑ r ∈ positiveExponents M, mu.expect (fun m : S ↦
        |divInd (p ^ r) (m : ℕ)| * |score m|)) ≤
      ∑ r ∈ positiveExponents M,
        (B / L) * ((1 / c) *
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hpr : 0 < p ^ r := pow_pos hp.pos r
      simpa only [mu, score] using
        uniformOnFinset_expect_abs_divInd_mul_abs_valuationScore_lcm_le
          S P hS eta hpr hM hB hL hc hcard hSpos hSle hprime heta
    _ = (B / L) * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]



end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry



theorem positivePrimePowerLcmConstant_pos :
    0 < positivePrimePowerLcmConstant := by
  unfold positivePrimePowerLcmConstant
  have hq : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity











end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]





/-- Closed reciprocal version of the marked first Taylor moment for a full
valuation row. -/
theorem uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_reciprocal_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M p : ℕ} {B L c : ℝ}
    (hpP : p ∈ P) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuation p (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * (1 / c) *
        ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
          positivePrimePowerLcmConstant) / (p : ℝ)) := by
  have hraw := uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_le
    S P hS eta (hprime p hpP) hM hB hL hc hcard hSpos hSle hprime heta
  have hledger := sum_positiveExponents_primePowerModuli_inv_lcm_le
    P M p hpP hprime
  have hfactor0 : 0 ≤ (B / L) * (1 / c) := by positivity
  calc
    _ ≤ (B / L) * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := hraw
    _ = ((B / L) * (1 / c)) *
        (∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by ring
    _ ≤ ((B / L) * (1 / c)) *
        ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
          positivePrimePowerLcmConstant) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hledger hfactor0
    _ = (B / L) * (1 / c) *
        ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
          positivePrimePowerLcmConstant) / (p : ℝ)) := by ring

/-- Unmarked first moment of the literal valuation score. -/
theorem uniformOnFinset_expect_abs_valuationScore_reciprocal_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M : ℕ} {B L c : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ)) := by
  have hraw := uniformOnFinset_expect_abs_divInd_mul_abs_valuationScore_lcm_le
    S P hS eta (D := 1) (by omega) hM hB hL hc hcard hSpos hSle
      hprime heta
  have hleft : (fun m : S ↦
      |divInd 1 (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) =
      fun m : S ↦ |valuationScore P eta L (m : ℕ)| := by
    funext m
    simp [divInd]
  rw [hleft] at hraw
  simp only [Nat.lcm_one_left] at hraw
  have hsum := sum_inv_primePowerModuli_le P M hprime
  have hfactor0 : 0 ≤ (B / L) * (1 / c) := by positivity
  calc
    _ ≤ (B / L) * ((1 / c) *
        ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) := hraw
    _ = ((B / L) * (1 / c)) *
        (∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) := by ring
    _ ≤ ((B / L) * (1 / c)) *
        (2 * ∑ q ∈ P, 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hfactor0
    _ = (B / L) * ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ)) := by ring



/-- Reciprocal first moment of one full valuation under the un-tilted
uniform cell law. -/
theorem uniformOnFinset_expect_valuation_reciprocal_le
    (S : Finset ℕ) (hS : S.Nonempty) {M p : ℕ} {c : ℝ}
    (hp : p.Prime) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    (uniformOnFinset S hS).expect
        (fun m : S ↦ (valuation p (m : ℕ) : ℝ)) ≤
      2 / (c * (p : ℝ)) := by
  let mu := uniformOnFinset S hS
  have hpoint : (fun m : S ↦ (valuation p (m : ℕ) : ℝ)) =
      fun m : S ↦ ∑ r ∈ positiveExponents M,
        divInd (p ^ r) (m : ℕ) := by
    funext m
    exact valuation_eq_sum_divInd_of_le hp (hSpos m m.property)
      (hSle m m.property)
  rw [hpoint,
    PrimePowerCutoffCovariance.FiniteProbability.expect_sum]
  have hterm (r : ℕ) (hr : r ∈ positiveExponents M) :
      mu.expect (fun m : S ↦ divInd (p ^ r) (m : ℕ)) ≤
        1 / (c * ((p ^ r : ℕ) : ℝ)) := by
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    exact OmittedTiltFallback.uniformAverage_divInd_le S
      (pow_pos hp.pos r) hM hc hcard hSpos hSle
  calc
    ∑ r ∈ positiveExponents M,
        mu.expect (fun m : S ↦ divInd (p ^ r) (m : ℕ)) ≤
      ∑ r ∈ positiveExponents M,
        1 / (c * ((p ^ r : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum fun r hr ↦ hterm r hr
    _ = (1 / c) * (∑ r ∈ positiveExponents M,
        1 / ((p ^ r : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ (1 / c) * (2 / (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_inv_prime_powers_le p M hp.two_le) (by positivity)
    _ = 2 / (c * (p : ℝ)) := by ring







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

/- Source module: Erdos390.Full.PaperRawPrefixValuationRow -/
section


/-!
# The raw full-valuation moving-prefix row

This file sums the divisor-prefix estimates over the exact local prime-power
cutoff.  Prime powers in the four-mark chamber use the sharp moving-prefix
estimate.  The remaining powers use the reciprocal fallback and the literal
weighted diagonal tail ledger.  The result is an explicit `p⁻¹` row whose
coefficient tends to zero at the rate required in paper Lemma 8.6.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance PrimePowerCutoffCovariance
open PaperPrimePowerTailLedger LocalFugacityBounds ValuationCutoff
open PaperPrimePowerTailRow

noncomputable section

namespace PaperRawPrefixValuationRow



/-- The explicit tail in `exists_uniform_rawCell_valuation_prefix_bound`,
after multiplication by its row prime, is absorbed by the already audited
common tail-row majorant. -/
theorem eventually_rawValuationPrefix_rowCoefficient_le
    (K G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ p ∈ primeBand n W,
      (p : ℝ) *
          ((2 * K / L n) * (1 / (p : ℝ)) +
            (4 * G * (cutoffScale W * L n) ^ 2) /
              ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
        rawValuationPrefixRateMajorant K G W n := by
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  intro p hpBand
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hKscale : 0 ≤ (cutoffScale W * L n) ^ 2 := sq_nonneg _
  have hYsq : 0 ≤ (yNat n : ℝ) ^ 2 := sq_nonneg _
  have htail0 : 0 ≤ tailRowMajorant G W n :=
    tailRowMajorant_nonneg hG hW hn
  have htailPiece :
      (p : ℝ) *
          ((4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
        6 * G *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
    have hnum : 0 ≤ 4 * G * (cutoffScale W * L n) ^ 2 := by positivity
    have hpInv : (1 : ℝ) / p ≤ 1 := by
      simpa using one_div_le_one_div_of_le
        (show (0 : ℝ) < 1 by norm_num) hpR
    calc
      (p : ℝ) *
          ((4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) =
        (4 * G) * (1 / (p : ℝ)) *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
        field_simp [hpR0.ne']
      _ ≤ (4 * G) * 1 *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
        gcongr
      _ ≤ 6 * G *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) := by
        have hratio : 0 ≤
            (cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2 :=
          div_nonneg hKscale hYsq
        nlinarith
  have hpieceLe :
      6 * G *
          ((cutoffScale W * L n) ^ 2 / (yNat n : ℝ) ^ 2) ≤
        tailRowMajorant G W n := by
    unfold tailRowMajorant
    dsimp only
    have hT : 0 ≤ G + G ^ 2 := by nlinarith [sq_nonneg G]
    have hband : 0 ≤ PrimeSums.bandReciprocalSum n W := by
      unfold PrimeSums.bandReciprocalSum
      positivity
    have hscale : 0 ≤ cutoffScale W * L n :=
      mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
    have hY : 0 ≤ (yNat n : ℝ) := by positivity
    have hYrpow : 0 ≤ (yNat n : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_nonneg hY _
    exact le_add_of_nonneg_left (add_nonneg
      (mul_nonneg hT (mul_nonneg (div_nonneg hscale hY)
        (by linarith)))
      (mul_nonneg hT (div_nonneg hKscale hYrpow)))
  unfold rawValuationPrefixRateMajorant
  calc
    (p : ℝ) *
        ((2 * K / L n) * (1 / (p : ℝ)) +
          (4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) =
      2 * K / L n +
        (p : ℝ) *
          ((4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
      field_simp [hpR0.ne']
    _ ≤ 2 * K / L n + tailRowMajorant G W n :=
      add_le_add_right (htailPiece.trans hpieceLe) _

/-- The raw un-tilted moving-prefix row survives the additional moving-low
harmonic loss. -/
theorem tendsto_rawValuationPrefixRateMajorant_mul_logL_zero
    (K G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Filter.Tendsto (fun n : ℕ ↦
      rawValuationPrefixRateMajorant K G W n * Real.log (L n))
      Filter.atTop (nhds 0) := by
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (L n) / L n)
      Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hfirst : Filter.Tendsto
      (fun n : ℕ ↦ (2 * K / L n) * Real.log (L n))
      Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _n : ℕ ↦ 2 * K)
        Filter.atTop (nhds (2 * K)) := tendsto_const_nhds
    have hraw := hconst.mul hone
    have heq :
        (fun n : ℕ ↦ (2 * K / L n) * Real.log (L n)) =
          fun n : ℕ ↦ 2 * K * (Real.log (L n) / L n) := by
      funext n
      ring
    rw [heq]
    simpa only [mul_zero] using hraw
  have htail := tendsto_tailRowMajorant_mul_logL_zero G W hG hW
  unfold rawValuationPrefixRateMajorant
  simpa only [add_mul, zero_add] using hfirst.add htail



end PaperRawPrefixValuationRow

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperRawTiltTaylorRate -/
section


/-!
# A closed rate bound for the raw moving-prefix Taylor polynomial

The finite Taylor theorem records its normalization and remainder terms in
`rawTiltPrefixTaylorBound`.  For the asymptotic application we only need a
simple domination by the marked first moment `RFone` and by `MF * a`.
This file proves that domination with a fixed numerical constant, so the
subsequent rate argument does not have to re-expand the polynomial.
-/

open Filter Topology

namespace Erdos390.Full

open ArithmeticModel Scale PrimeSums

noncomputable section

namespace FiniteProbability









/-- The literal nonlinear Taylor row, multiplied by its row prime, is
eventually bounded by `rawTiltNonlinearRateMajorant`.  The assertion is
uniform in every positive prime and therefore in the entire moving band. -/
theorem eventually_rawTiltNonlinear_row_le
    (B c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      let H := bandReciprocalSum n W
      let a := (B / L n) * ((2 / c) * H)
      let MF := 2 / (c * (p : ℝ))
      let RFone := (B / L n) * (1 / c) *
        ((4 * H + PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
          (p : ℝ))
      (p : ℝ) * (128 * (RFone + MF * a)) ≤
        rawTiltNonlinearRateMajorant B c n := by
  filter_upwards [eventually_bandReciprocalSum_le_logL W,
    Filter.eventually_gt_atTop 2] with n hband hn
  intro p hp
  dsimp only
  have hL : 0 < L n := L_pos (by omega)
  have hlog : 0 ≤ Real.log (L n) := by
    apply Real.log_nonneg
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
    have hnCast : (Real.exp 1 : ℝ) ≤ (n : ℝ) :=
      Real.exp_one_lt_three.le.trans h3
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < n)).2
      (by simpa only [L] using hnCast)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hH0 : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hHstar0 : 0 ≤ 12 * Real.log (L n) := by positivity
  have hcoef1 : 0 ≤ (B / L n) * (1 / c) := by positivity
  have hcoef2 : 0 ≤ (2 / c) * (B / L n) * (2 / c) := by positivity
  have heq :
      (p : ℝ) *
          (128 *
            ((B / L n) * (1 / c) *
                ((4 * bandReciprocalSum n W +
                    PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
                  (p : ℝ)) +
              (2 / (c * (p : ℝ))) *
                ((B / L n) *
                  ((2 / c) * bandReciprocalSum n W)))) =
        128 *
          ((B / L n) * (1 / c) *
              (4 * bandReciprocalSum n W +
                PrimePowerTaylorLedger.positivePrimePowerLcmConstant) +
            (2 / c) * ((B / L n) *
              ((2 / c) * bandReciprocalSum n W))) := by
    field_simp [hpR.ne', hc.ne', hL.ne']
  rw [heq]
  unfold rawTiltNonlinearRateMajorant
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hcoef1
    gcongr
  · calc
      (2 / c) *
          ((B / L n) * ((2 / c) * bandReciprocalSum n W)) =
          ((2 / c) * (B / L n) * (2 / c)) *
            bandReciprocalSum n W := by ring
      _ ≤ ((2 / c) * (B / L n) * (2 / c)) *
          (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef2
      _ = (2 / c) *
          ((B / L n) * ((2 / c) * (12 * Real.log (L n)))) := by ring

/-- The nonlinear Taylor row survives the additional moving-low harmonic
loss. -/
theorem tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero
    (B c : ℝ) :
    Tendsto (fun n : ℕ ↦
      rawTiltNonlinearRateMajorant B c n * Real.log (L n))
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto
      (fun n : ℕ ↦ Real.log (L n) ^ 2 / L n) atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hone : Tendsto
      (fun n : ℕ ↦ Real.log (L n) / L n) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  let A₁ : ℝ := 128 * (48 * B / c + 48 * B / c ^ 2)
  let A₂ : ℝ := 128 *
    (B / c * PrimePowerTaylorLedger.positivePrimePowerLcmConstant)
  have hlimit : Tendsto (fun n : ℕ ↦
      A₁ * (Real.log (L n) ^ 2 / L n) +
        A₂ * (Real.log (L n) / L n)) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hsq).add (tendsto_const_nhds.mul hone)
  apply hlimit.congr'
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  unfold rawTiltNonlinearRateMajorant
  dsimp only
  dsimp only [A₁, A₂]
  ring

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperRawTiltedPrefixRow -/
section


/-!
# The raw tilted full-valuation moving-prefix row

This file closes the finite Taylor argument for the nuisance marked rows.
All inputs to the Taylor lemma are discharged from the structured-cell
census, the un-tilted prefix theorem, and the third-cumulant theorem.  The
only scale separation retained in the terminal statement is the transparent
fixed-box condition `2 B ≤ log W`, which makes the valuation score pointwise
at most one.  The resulting row coefficient remains `o(1 / log L)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimeSums ValuationScoreDomination ValuationTiltCell
open PaperScaleMarkedCell FullTiltPairChamber
open PaperRawPrefixValuationRow PaperRawPrefixThirdCumulantRow

noncomputable section

namespace PaperRawTiltedPrefixRow



/-- For a fixed box and fixed positive cell-density lower bound, the Taylor
smallness parameter tends to zero.  This statement is uniform in all
coefficients in the box because it only contains the box radius `B`. -/
theorem tendsto_rawTiltSmallParameter_zero
    (B c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    Tendsto (rawTiltSmallParameter B c W) atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto
      (fun n : ℕ ↦ (24 * B / c) * (Real.log (L n) / L n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hratio
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ rawTiltSmallParameter B c W n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    unfold rawTiltSmallParameter bandReciprocalSum
    have hL : 0 < L n := L_pos hn
    positivity
  have hle : ∀ᶠ n : ℕ in atTop,
      rawTiltSmallParameter B c W n ≤
        (24 * B / c) * (Real.log (L n) / L n) := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      Filter.eventually_gt_atTop 1] with n hband hn
    have hL : 0 < L n := L_pos hn
    have hcoef : 0 ≤ (B / L n) * (2 / c) := by positivity
    unfold rawTiltSmallParameter
    calc
      (B / L n) * ((2 / c) * bandReciprocalSum n W) =
          ((B / L n) * (2 / c)) * bandReciprocalSum n W := by ring
      _ ≤ ((B / L n) * (2 / c)) * (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef
      _ = (24 * B / c) * (Real.log (L n) / L n) := by ring
  exact squeeze_zero' hnonneg hle hmajor







end PaperRawTiltedPrefixRow

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBoundedScorePrefixCovariance -/
section


/-!
# Localized covariance transport on an arbitrary fixed score box

The Taylor wrapper used previously normalized the pointwise score to one.
For the paper's parameter order the coefficient box is chosen after `W`, so
that normalization must not survive as a terminal hypothesis.  The lemmas
below instead use the exact exponential change of measure.  A fixed score
box contributes only `exp K`; the small quantity is the first absolute
score moment.  Marked first moments retain their reciprocal-prime scale.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- A nonnegative mark need not be pointwise bounded.  Under an arbitrary
fixed score box, its expectation changes on the scale of its marked first
score moment plus its mean times the unmarked first score moment. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
    (mu : FiniteProbability Omega) (F S : Omega → ℝ)
    {K a MF RF : ℝ}
    (hF0 : ∀ omega, 0 ≤ F omega)
    (hscore : ∀ omega, |S omega| ≤ K)
    (ha0 : 0 ≤ a) (hMF0 : 0 ≤ MF) (hRF0 : 0 ≤ RF)
    (hsmall : Real.exp K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hmeanF : mu.expect F ≤ MF)
    (hmarked : mu.expect (fun omega ↦ F omega * |S omega|) ≤ RF) :
    |(mu.exponentialTilt S).expect F - mu.expect F| ≤
      2 * Real.exp K * (RF + MF * a) := by
  let Z := mu.expPartition S
  let m := mu.expect F
  let N := mu.expect (fun omega ↦ F omega * Real.exp (S omega))
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation F S
  have hm0 : 0 ≤ m := by
    dsimp only [m]
    exact mu.expect_nonneg F hF0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have heta0 : 0 ≤ eta :=
    mu.markedExponentialDeviation_nonneg F S hF0
  have hdelta : delta ≤ Real.exp K * a := by
    exact (mu.exponentialDeviation_le_exp_mul_expect_abs S hscore).trans
      (mul_le_mul_of_nonneg_left habsScore (Real.exp_pos K).le)
  have hdeltaHalf : delta ≤ (1 : ℝ) / 2 := hdelta.trans hsmall
  have hdeltaOne : delta < 1 := hdeltaHalf.trans_lt (by norm_num)
  have hZpos : 0 < Z := mu.expPartition_pos S
  have hZhalf : (1 : ℝ) / 2 ≤ Z := by
    have hlower := mu.expPartition_lower_bound S
    dsimp only [Z]
    linarith
  have hN : |N - m| ≤ eta := by
    dsimp only [N, m]
    exact mu.abs_expWeighted_expect_sub_expect_le F S hF0
  have hZ : |Z - 1| ≤ delta := by
    dsimp only [Z, delta]
    exact mu.abs_expPartition_sub_one_le_deviation S
  have heta : eta ≤ Real.exp K * RF := by
    exact (mu.markedExponentialDeviation_le_exp_mul_expect_abs
      F S hF0 hscore).trans
        (mul_le_mul_of_nonneg_left hmarked (Real.exp_pos K).le)
  rw [mu.exponentialTilt_expect_eq F S]
  change |N / Z - m| ≤ _
  have hid : N / Z - m = ((N - m) + m * (1 - Z)) / Z := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hZpos]
  have hnum : |(N - m) + m * (1 - Z)| ≤
      Real.exp K * (RF + MF * a) := by
    calc
      |(N - m) + m * (1 - Z)| ≤ |N - m| + |m * (1 - Z)| :=
        abs_add_le _ _
      _ = |N - m| + m * |Z - 1| := by
        rw [abs_mul, abs_of_nonneg hm0, abs_sub_comm 1 Z]
      _ ≤ eta + MF * delta := by
        exact add_le_add hN
          (mul_le_mul hmeanF hZ (abs_nonneg _) hMF0)
      _ ≤ Real.exp K * RF + MF * (Real.exp K * a) := by
        exact add_le_add heta
          (mul_le_mul_of_nonneg_left hdelta hMF0)
      _ = Real.exp K * (RF + MF * a) := by ring
  have htarget0 : 0 ≤ Real.exp K * (RF + MF * a) := by positivity
  calc
    |(N - m) + m * (1 - Z)| / Z ≤
        (Real.exp K * (RF + MF * a)) / Z :=
      div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (Real.exp K * (RF + MF * a)) / ((1 : ℝ) / 2) := by
      exact div_le_div_of_nonneg_left htarget0 (by norm_num) hZhalf
    _ = 2 * Real.exp K * (RF + MF * a) := by ring

/-- Covariance with a `[0,1]` prefix is stable on the same marked scale.
The conclusion displays the exact two expectation-loss coefficients used
downstream; no pointwise-small relation between `K` and the prime cutoff is
assumed. -/
theorem abs_exponentialTilt_covariance_prefix_sub_covariance_le_of_bounded_score
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {K a MF RF : ℝ}
    (hF0 : ∀ omega, 0 ≤ F omega)
    (hG0 : ∀ omega, 0 ≤ G omega)
    (hG1 : ∀ omega, G omega ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ K)
    (ha0 : 0 ≤ a) (hMF0 : 0 ≤ MF) (hRF0 : 0 ≤ RF)
    (hsmall : Real.exp K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hmeanF : mu.expect F ≤ MF)
    (hmarkedF : mu.expect (fun omega ↦ F omega * |S omega|) ≤ RF) :
    let DF := 2 * Real.exp K * (RF + MF * a)
    let DG := 4 * Real.exp K * a
    |(mu.exponentialTilt S).covariance F G - mu.covariance F G| ≤
      DF + (MF + DF) * DG + DF := by
  dsimp only
  let DF : ℝ := 2 * Real.exp K * (RF + MF * a)
  let DG : ℝ := 4 * Real.exp K * a
  have hDF0 : 0 ≤ DF := by dsimp only [DF]; positivity
  have hDG0 : 0 ≤ DG := by dsimp only [DG]; positivity
  have hmeanG : mu.expect G ≤ 1 := by
    calc
      mu.expect G ≤ mu.expect (fun _ ↦ (1 : ℝ)) :=
        mu.expect_mono G _ hG1
      _ = 1 := by
        unfold expect
        rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hmarkedG : mu.expect (fun omega ↦ G omega * |S omega|) ≤ a := by
    calc
      mu.expect (fun omega ↦ G omega * |S omega|) ≤
          mu.expect (fun omega ↦ |S omega|) := by
        apply mu.expect_mono
        intro omega
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hG1 omega) (abs_nonneg (S omega))
      _ ≤ a := habsScore
  have hFG0 : ∀ omega, 0 ≤ F omega * G omega := fun omega ↦
    mul_nonneg (hF0 omega) (hG0 omega)
  have hFGle : ∀ omega, F omega * G omega ≤ F omega := by
    intro omega
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hG1 omega) (hF0 omega)
  have hmeanFG : mu.expect (fun omega ↦ F omega * G omega) ≤ MF :=
    (mu.expect_mono _ F hFGle).trans hmeanF
  have hmarkedFG : mu.expect
      (fun omega ↦ (F omega * G omega) * |S omega|) ≤ RF := by
    calc
      mu.expect (fun omega ↦ (F omega * G omega) * |S omega|) ≤
          mu.expect (fun omega ↦ F omega * |S omega|) := by
        apply mu.expect_mono
        intro omega
        exact mul_le_mul_of_nonneg_right (hFGle omega) (abs_nonneg _)
      _ ≤ RF := hmarkedF
  have hFperturb :
      |(mu.exponentialTilt S).expect F - mu.expect F| ≤ DF := by
    simpa only [DF] using
      mu.abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
        F S hF0 hscore ha0 hMF0 hRF0 hsmall habsScore hmeanF hmarkedF
  have hGperturb :
      |(mu.exponentialTilt S).expect G - mu.expect G| ≤ DG := by
    have hraw :=
      mu.abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
        G S hG0 hscore ha0 (by norm_num : (0 : ℝ) ≤ 1) ha0
        hsmall habsScore hmeanG hmarkedG
    convert hraw using 1
    dsimp only [DG]
    ring
  have hFGperturb :
      |(mu.exponentialTilt S).expect (fun omega ↦ F omega * G omega) -
          mu.expect (fun omega ↦ F omega * G omega)| ≤ DF := by
    simpa only [DF] using
      mu.abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
        (fun omega ↦ F omega * G omega) S hFG0 hscore ha0 hMF0 hRF0
        hsmall habsScore hmeanFG hmarkedFG
  simpa only [DF, DG, one_mul] using
    (abs_covariance_sub_covariance_le_of_expectation_perturbations
      mu (mu.exponentialTilt S) F G hF0 hG0 hmeanF hmeanG hDF0
        hFperturb hGperturb hFGperturb)

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted -/
section


/-!
# Raw tilted moving-prefix row with an unrestricted fixed coefficient box

This is the parameter-order-safe form of the raw row.  `W` and the box
radius are arbitrary fixed parameters.  The score envelope
`2 B / log W` enters only through a fixed exponential constant; no relation
between the box radius and `W` is assumed.
-/

open Filter Topology

namespace Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimeSums ValuationScoreDomination ValuationTiltCell
open PaperScaleMarkedCell FullTiltPairChamber
open PaperRawPrefixValuationRow
open PaperRawTiltedPrefixRow

noncomputable section

set_option maxHeartbeats 1600000

/-- The raw moving-prefix terminal for arbitrary fixed `B,W`. -/
theorem exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
    ∃ epsilon : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → physicalBound A n < k →
        k ≤ physicalBound C n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) := by
  let c : ℝ := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  obtain ⟨K₀, hK₀, G₀, hG₀, Nbase, hbase⟩ :=
    exists_uniform_rawCell_valuation_prefix_bound
      H hA hAC hC W hW hHeadLe
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let Kscore : ℝ := (2 * B) / Real.log (W : ℝ)
  let epsilonZero : ℕ → ℝ := rawValuationPrefixRateMajorant K₀ G₀ W
  let epsilonPerturb : ℕ → ℝ := fun n ↦
    Real.exp Kscore * rawTiltNonlinearRateMajorant B c n
  let epsilon : ℕ → ℝ := fun n ↦ epsilonZero n + epsilonPerturb n
  have hepsilonZero : Tendsto (fun n : ℕ ↦
      epsilonZero n * Real.log (L n)) atTop (nhds 0) :=
    tendsto_rawValuationPrefixRateMajorant_mul_logL_zero
      K₀ G₀ W hG₀.le hW
  have hepsilonPerturb : Tendsto (fun n : ℕ ↦
      epsilonPerturb n * Real.log (L n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ Real.exp Kscore)
        atTop (nhds (Real.exp Kscore)) := tendsto_const_nhds
    have hrate := tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero B c
    have hmul := hconst.mul hrate
    simpa only [epsilonPerturb, mul_zero, mul_assoc] using hmul
  have hepsilon : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := hepsilonZero.add hepsilonPerturb
    simpa only [epsilon, add_mul, zero_add] using hsum
  have hbaseRate := eventually_rawValuationPrefix_rowCoefficient_le
    K₀ G₀ W hG₀.le hW
  have hnonlinearRate :=
    eventually_rawTiltNonlinear_row_le B c W hB hc
  have haT := tendsto_rawTiltSmallParameter_zero B c W hB hc
  have hEaT : Tendsto (fun n : ℕ ↦
      Real.exp Kscore * rawTiltSmallParameter B c W n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul haT
  have hsmallHalf : ∀ᶠ n : ℕ in atTop,
      Real.exp Kscore * rawTiltSmallParameter B c W n ≤
        (1 : ℝ) / 2 :=
    hEaT.eventually (eventually_le_nhds (by norm_num))
  have hsmallQuarter : ∀ᶠ n : ℕ in atTop,
      4 * Real.exp Kscore * rawTiltSmallParameter B c W n ≤ 1 := by
    filter_upwards [hEaT.eventually (eventually_le_nhds
      (by norm_num : (0 : ℝ) < 1 / 4))] with n hn
    linarith
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  have hAll : ∀ᶠ n : ℕ in atTop,
      (∀ p ∈ primeBand n W,
        (p : ℝ) *
            ((2 * K₀ / L n) * (1 / (p : ℝ)) +
              (4 * G₀ *
                  (PaperPrimePowerTailLedger.cutoffScale W * L n) ^ 2) /
                ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
          epsilonZero n) ∧
      (∀ p : ℕ, 0 < p →
        let Hsum := bandReciprocalSum n W
        let a := (B / L n) * ((2 / c) * Hsum)
        let MF := 2 / (c * (p : ℝ))
        let RFone := (B / L n) * (1 / c) *
          ((4 * Hsum +
              PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
            (p : ℝ))
        (p : ℝ) * (128 * (RFone + MF * a)) ≤
          rawTiltNonlinearRateMajorant B c n) ∧
      Real.exp Kscore * rawTiltSmallParameter B c W n ≤ (1 : ℝ) / 2 ∧
      4 * Real.exp Kscore * rawTiltSmallParameter B c W n ≤ 1 ∧
      C ≤ (n : ℝ) ∧ 1 / C ≤ (n : ℝ) ∧ 2 < n := by
    filter_upwards [hbaseRate, hnonlinearRate, hsmallHalf, hsmallQuarter,
      hCevent, hInvCevent, Filter.eventually_gt_atTop 2] with
      n hbaseN hnonlinearN hhalfN hquarterN hCn hInvCn hn
    exact ⟨hbaseN, hnonlinearN, hhalfN, hquarterN, hCn, hInvCn, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨epsilon, hepsilon, max Nbase (max Ndensity Nevent), ?_⟩
  intro n k p eta hN hlow hhigh hpBand heta
  have hNbase : Nbase ≤ n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNevent' : Nevent ≤ n := by omega
  obtain ⟨hbaseRateN, hnonlinearRateN, hhalfN, hquarterN,
    hCn, hInvCn, hn⟩ := hNevent n hNevent'
  have hL : 0 < L n := L_pos (by omega)
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let M := physicalBound C n
  let S := structuredCell H (physicalBound A n) M (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  have hMcast : (M : ℝ) ≤ C * (n : ℝ) := by
    dsimp only [M]
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hMlower : 1 ≤ M := by
    dsimp only [M]
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have hraw := (div_le_iff₀ hC).mp hInvCn
      simpa only [one_mul, mul_comm] using hraw
    exact_mod_cast hOne
  have hMpos : 0 < M := Nat.zero_lt_of_lt hMlower
  have hcard : c * (M : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (M : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hC.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S, M] using hdensity hNdensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ M := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  have hprime : ∀ q ∈ primeBand n W, q.Prime := by
    intro q hq
    exact prime_of_mem_primeBand hq
  have hpW : ∀ q ∈ primeBand n W, W ≤ q := by
    intro q hq
    exact (cutoff_lt_of_mem_primeBand hq).le
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogM : Real.log (M : ℝ) ≤ 2 * L n := by
    have hMleSq : (M : ℝ) ≤ (n : ℝ) ^ 2 := hMcast.trans hCnSq
    have hraw := Real.log_le_log (by exact_mod_cast hMpos) hMleSq
    rw [Real.log_pow] at hraw
    simpa [L] using hraw
  have hscore : ∀ m : S,
      |valuationScore (primeBand n W) eta (L n) (m : ℕ)| ≤ Kscore := by
    intro m
    have hraw := abs_valuationScore_le_log_ratio
      (primeBand n W) eta (hSpos m m.property) (hSle m m.property)
      hW hpW hB hL heta
    calc
      |valuationScore (primeBand n W) eta (L n) (m : ℕ)| ≤
          (B / L n) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := hraw
      _ ≤ (B / L n) * ((2 * L n) / Real.log (W : ℝ)) := by
        gcongr
      _ = Kscore := by
        dsimp only [Kscore]
        field_simp [hL.ne', hlogW.ne']
  let mu := uniformOnFinset S hS
  let score : S → ℝ := fun m ↦
    valuationScore (primeBand n W) eta (L n) (m : ℕ)
  let F : S → ℝ := fun m ↦ (valuation p (m : ℕ) : ℝ)
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  let Czero : ℝ :=
    (2 * K₀ / L n) * (1 / (p : ℝ)) +
      (4 * G₀ * (PaperPrimePowerTailLedger.cutoffScale W * L n) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)
  let a : ℝ := rawTiltSmallParameter B c W n
  let MF : ℝ := 2 / (c * (p : ℝ))
  let RFone : ℝ := (B / L n) * (1 / c) *
    ((4 * bandReciprocalSum n W +
      PrimePowerTaylorLedger.positivePrimePowerLcmConstant) / (p : ℝ))
  let X : ℝ := RFone + MF * a
  let DF : ℝ := 2 * Real.exp Kscore * X
  let DG : ℝ := 4 * Real.exp Kscore * a
  have ha0 : 0 ≤ a := by
    dsimp only [a, rawTiltSmallParameter, bandReciprocalSum]
    positivity
  have hMF0 : 0 ≤ MF := by dsimp only [MF]; positivity
  have hRF0 : 0 ≤ RFone := by
    dsimp only [RFone, bandReciprocalSum]
    have hconst := PrimePowerTaylorLedger.positivePrimePowerLcmConstant_pos
    positivity
  have hX0 : 0 ≤ X := by dsimp only [X]; positivity
  have hDF0 : 0 ≤ DF := by dsimp only [DF]; positivity
  have hDG0 : 0 ≤ DG := by dsimp only [DG]; positivity
  have hDG1 : DG ≤ 1 := by
    simpa only [DG, a] using hquarterN
  have hF0 : ∀ m, 0 ≤ F m := by
    intro m
    exact valuation_nonneg p (m : ℕ)
  have hpref0 : ∀ m, 0 ≤ pref m := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hpref1 : ∀ m, pref m ≤ 1 := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have habsScore : mu.expect (fun m ↦ |score m|) ≤ a := by
    dsimp only [mu, score, a, rawTiltSmallParameter]
    exact uniformOnFinset_expect_abs_valuationScore_reciprocal_le
      S (primeBand n W) hS eta hMpos hB hL hc hcard hSpos hSle
        hprime heta
  have hmeanF : mu.expect F ≤ MF := by
    dsimp only [mu, F, MF]
    exact uniformOnFinset_expect_valuation_reciprocal_le
      S hS hp hMpos hc hcard hSpos hSle
  have hmarkedF : mu.expect (fun m ↦ F m * |score m|) ≤ RFone := by
    have hraw :=
      uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_reciprocal_le
        S (primeBand n W) hS eta hpBand hMpos hB hL hc hcard
          hSpos hSle hprime heta
    simpa only [mu, F, score, abs_of_nonneg (hF0 _), RFone] using hraw
  have hbaseN : |mu.covariance F pref| ≤ Czero := by
    simpa only [mu, F, pref, S, M, Czero] using
      hbase hNbase hlow hhigh hpBand hS
  have hdiff : |(mu.exponentialTilt score).covariance F pref -
      mu.covariance F pref| ≤ DF + (MF + DF) * DG + DF := by
    have hraw :=
      mu.abs_exponentialTilt_covariance_prefix_sub_covariance_le_of_bounded_score
        F pref score hF0 hpref0 hpref1
          (by simpa only [score] using hscore) ha0 hMF0 hRF0
          (by simpa only [a] using hhalfN) habsScore hmeanF hmarkedF
    simpa only [DF, DG, X] using hraw
  have htilt : |(mu.exponentialTilt score).covariance F pref| ≤
      Czero + (DF + (MF + DF) * DG + DF) := by
    calc
      |(mu.exponentialTilt score).covariance F pref| =
          |mu.covariance F pref +
            ((mu.exponentialTilt score).covariance F pref -
              mu.covariance F pref)| := by
                congr 1
                ring
      _ ≤ |mu.covariance F pref| +
          |(mu.exponentialTilt score).covariance F pref -
            mu.covariance F pref| := abs_add_le _ _
      _ ≤ Czero + (DF + (MF + DF) * DG + DF) :=
        add_le_add hbaseN hdiff
  have hzeroRow : Czero ≤ epsilonZero n / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [Czero, epsilonZero, mul_comm] using
      hbaseRateN p hpBand
  have hnonlinear :
      (p : ℝ) * (128 * X) ≤ rawTiltNonlinearRateMajorant B c n := by
    simpa only [X, a, MF, RFone] using hnonlinearRateN p hp.pos
  have hMFpart : (p : ℝ) * MF * a ≤ (p : ℝ) * X := by
    dsimp only [X]
    nlinarith [mul_nonneg hpR.le hRF0]
  have hDFrow : (p : ℝ) * DF =
      2 * Real.exp Kscore * ((p : ℝ) * X) := by
    dsimp only [DF]
    ring
  have hMFDGrow : (p : ℝ) * MF * DG ≤
      4 * Real.exp Kscore * ((p : ℝ) * X) := by
    dsimp only [DG]
    have hE0 : 0 ≤ 4 * Real.exp Kscore := by positivity
    calc
      (p : ℝ) * MF * (4 * Real.exp Kscore * a) =
          (4 * Real.exp Kscore) * ((p : ℝ) * MF * a) := by ring
      _ ≤ (4 * Real.exp Kscore) * ((p : ℝ) * X) :=
        mul_le_mul_of_nonneg_left hMFpart hE0
  have hDFDGrow : (p : ℝ) * DF * DG ≤
      2 * Real.exp Kscore * ((p : ℝ) * X) := by
    calc
      (p : ℝ) * DF * DG ≤ (p : ℝ) * DF * 1 :=
        mul_le_mul_of_nonneg_left hDG1 (mul_nonneg hpR.le hDF0)
      _ = 2 * Real.exp Kscore * ((p : ℝ) * X) := by rw [mul_one, hDFrow]
  have hperturbRow : (p : ℝ) *
      (DF + (MF + DF) * DG + DF) ≤ epsilonPerturb n := by
    have hten : (p : ℝ) * (DF + (MF + DF) * DG + DF) ≤
        10 * Real.exp Kscore * ((p : ℝ) * X) := by
      calc
        (p : ℝ) * (DF + (MF + DF) * DG + DF) =
            (p : ℝ) * DF + (p : ℝ) * MF * DG +
              (p : ℝ) * DF * DG + (p : ℝ) * DF := by ring
        _ ≤ (2 * Real.exp Kscore * ((p : ℝ) * X)) +
            (4 * Real.exp Kscore * ((p : ℝ) * X)) +
            (2 * Real.exp Kscore * ((p : ℝ) * X)) +
            (2 * Real.exp Kscore * ((p : ℝ) * X)) := by
          exact add_le_add
            (add_le_add (add_le_add hDFrow.le hMFDGrow) hDFDGrow)
            hDFrow.le
        _ = 10 * Real.exp Kscore * ((p : ℝ) * X) := by ring
    calc
      (p : ℝ) * (DF + (MF + DF) * DG + DF) ≤
          10 * Real.exp Kscore * ((p : ℝ) * X) := hten
      _ ≤ Real.exp Kscore * ((p : ℝ) * (128 * X)) := by
        have hrow0 : 0 ≤ (p : ℝ) * X := mul_nonneg hpR.le hX0
        nlinarith [Real.exp_pos Kscore]
      _ ≤ Real.exp Kscore * rawTiltNonlinearRateMajorant B c n :=
        mul_le_mul_of_nonneg_left hnonlinear (Real.exp_pos Kscore).le
      _ = epsilonPerturb n := rfl
  have hperturb : DF + (MF + DF) * DG + DF ≤
      epsilonPerturb n / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [mul_comm] using hperturbRow
  calc
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))).covariance
        (fun m : S ↦ valuation p (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
      Czero + (DF + (MF + DF) * DG + DF) := by
        simpa only [mu, score, F, pref] using htilt
    _ ≤ epsilonZero n / (p : ℝ) + epsilonPerturb n / (p : ℝ) :=
      add_le_add hzeroRow hperturb
    _ = epsilon n / (p : ℝ) := by
      dsimp only [epsilon]
      ring



end

end Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted

end

theorem solution : Erdos390.RemainingAnalyticGoal004_007 := by
  exact @Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted.exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted
