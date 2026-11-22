-- Prove2me | solution 1 for Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:10:29.609248+00:00
-- url     : https://prove2.me/submissions/264b7d49-4b51-44c6-8b66-87fec00649e8

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
import Theorems.Thm_Erdos390_Full_LocalFugacityBounds_coefficientTail_le
import Theorems.Thm_Erdos390_Full_OmittedTiltHarmonicRate_exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_Full_TwoLocalRestorationBound_abs_pairRestoredNumerator_sub_expect_le


section
theorem Erdos390.Full.OmittedTiltHarmonicRate.exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate : Erdos390.RemainingAnalyticGoal001_005 := @Erdos390.Full.OmittedTiltHarmonicRate.exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate_compact
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

/- Source module: Erdos390.Full.StructuredCells -/
section


/-!
# Exact structured-cell reductions

This file defines the actual finite smooth intervals and exact head cells.
It proves the finite inclusion--exclusion identity before any use of a
friable-number asymptotic.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCells

open HeadPattern























theorem pow_mem_smoothNumbers {z p : ℕ}
    (hp : p ∈ Nat.smoothNumbers z) (e : ℕ) :
    p ^ e ∈ Nat.smoothNumbers z := by
  induction e with
  | zero => simp [Nat.mem_smoothNumbers]
  | succ e ih =>
      rw [pow_succ]
      exact Nat.mul_mem_smoothNumbers ih hp













end Erdos390.Full.StructuredCells

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

/- Source module: Erdos390.Full.LocalFugacity -/
section


/-!
# Exact restoration of one local fugacity

This proves the finite telescoping identity used when an omitted prime is
restored in the tilted measure.  The coefficients are the actual
`λ^a-λ^(a-1)` coefficients and the indicators are actual divisibility
indicators.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacity

open ArithmeticModel





theorem coefficient_pos (lam : ℝ) {a : ℕ} (ha : 0 < a) :
    coefficient lam a = lam ^ a - lam ^ (a - 1) := by
  simp [coefficient, ha.ne']





private theorem telescoping_power (lam : ℝ) (v : ℕ) :
    1 + ∑ a ∈ Finset.Icc 1 v, (lam ^ a - lam ^ (a - 1)) = lam ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      calc
        1 + ((∑ a ∈ Finset.Icc 1 v, (lam ^ a - lam ^ (a - 1))) +
            (lam ^ (v + 1) - lam ^ (v + 1 - 1))) =
            (1 + ∑ a ∈ Finset.Icc 1 v, (lam ^ a - lam ^ (a - 1))) +
              (lam ^ (v + 1) - lam ^ (v + 1 - 1)) := by ring
        _ = lam ^ v + (lam ^ (v + 1) - lam ^ (v + 1 - 1)) := by rw [ih]
        _ = lam ^ (v + 1) := by
          simp only [Nat.add_sub_cancel, pow_succ]
          ring

/-- The paper's exact local-factor identity, truncated at any exponent `A`
above the actual valuation. -/
theorem pow_valuation_eq_indicator_expansion {p m A : ℕ} (lam : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hA : m.factorization p ≤ A) :
    lam ^ m.factorization p =
      1 + ∑ a ∈ Finset.Icc 1 A,
        coefficient lam a * divInd (p ^ a) m := by
  simp only [divInd, hp.pow_dvd_iff_le_factorization hm.ne']
  have hcoeff :
      (∑ a ∈ Finset.Icc 1 A,
        coefficient lam a * if a ≤ m.factorization p then 1 else 0) =
      ∑ a ∈ Finset.Icc 1 A,
        (lam ^ a - lam ^ (a - 1)) *
          if a ≤ m.factorization p then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a haMem
    have ha : 0 < a := by
      simp at haMem
      omega
    rw [coefficient_pos lam ha]
  rw [hcoeff]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 A).filter (fun a ↦ a ≤ m.factorization p) =
        Finset.Icc 1 (m.factorization p) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, telescoping_power]



end Erdos390.Full.LocalFugacity

end

/- Source module: Erdos390.Full.LocalFugacityRestoration -/
section


/-!
# Exact restoration of omitted local fugacities

The paper omits one or two forced primes from the global score and then
restores their local fugacity by a finite divisor-indicator expansion.  This
file proves that restoration identity for the actual valuation and for an
actual finite probability law.  No approximation or independence assumption
is used here.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityRestoration

open ArithmeticModel LocalFugacity

noncomputable section



private theorem Icc_zero_eq_insert (A : ℕ) :
    Finset.Icc 0 A = insert 0 (Finset.Icc 1 A) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- The finite local factor is exactly `λ^{v_p(m)}` once the cutoff is above
the actual valuation. -/
theorem localFactor_eq_pow_valuation {p m A : ℕ} (lam : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hA : m.factorization p ≤ A) :
    localFactor p A lam m = lam ^ m.factorization p := by
  rw [localFactor, Icc_zero_eq_insert]
  have hzero : 0 ∉ Finset.Icc 1 A := by simp
  rw [Finset.sum_insert hzero]
  simp only [coefficient_zero, pow_zero, one_mul]
  have hdiv : divInd 1 m = 1 := by simp [divInd]
  rw [hdiv]
  symm
  exact pow_valuation_eq_indicator_expansion lam hp hm hA









/-- Literal double-sum expansion of two restored local factors. -/
theorem localFactor_mul_eq_double_sum (p q A B : ℕ) (lam mu : ℝ) (m : ℕ) :
    localFactor p A lam m * localFactor q B mu m =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          (divInd (p ^ a) m * divInd (q ^ b) m) := by
  unfold localFactor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- For distinct primes, the product of the two actual divisor indicators is
the indicator of the product divisor. -/
theorem divInd_primePowers_mul {p q a b m : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    divInd (p ^ a) m * divInd (q ^ b) m =
      divInd (p ^ a * q ^ b) m := by
  by_cases hpa : p ^ a ∣ m
  · by_cases hqb : q ^ b ∣ m
    · have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
        (hp.coprime_iff_not_dvd.mpr (by
          intro hdiv
          exact hpq (Nat.dvd_prime hq |>.mp hdiv |>.resolve_left hp.ne_one))).pow
          a b
      have hprod : p ^ a * q ^ b ∣ m :=
        hcop.mul_dvd_of_dvd_of_dvd hpa hqb
      simp [divInd, hpa, hqb, hprod]
    · have hnprod : ¬p ^ a * q ^ b ∣ m := by
        intro hprod
        exact hqb ((dvd_mul_left (q ^ b) (p ^ a)).trans hprod)
      simp [divInd, hpa, hqb, hnprod]
  · have hnprod : ¬p ^ a * q ^ b ∣ m := by
      intro hprod
      exact hpa ((dvd_mul_right (p ^ a) (q ^ b)).trans hprod)
    simp [divInd, hpa, hnprod]

/-- The paper's exact two-local coefficient formula for distinct primes. -/
theorem localFactor_mul_eq_product_indicator {p q A B : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    (lam mu : ℝ) (m : ℕ) :
    localFactor p A lam m * localFactor q B mu m =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          divInd (p ^ a * q ^ b) m := by
  rw [localFactor_mul_eq_double_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [divInd_primePowers_mul hpq hp hq]

section Probability

variable {Omega : Type*} [Fintype Omega]

/-- Exact numerator after restoring two omitted local fugacities and imposing
a further divisor event `D ∣ m`. -/
theorem expect_two_restored_indicator
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q A B D : ℕ} (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    (lam mu : ℝ) :
    nu.expect (fun omega ↦
        divInd D (value omega) * localFactor p A lam (value omega) *
          localFactor q B mu (value omega)) =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          nu.expect (fun omega ↦
            divInd D (value omega) *
              divInd (p ^ a * q ^ b) (value omega)) := by
  have hpoint (omega : Omega) :
      divInd D (value omega) * localFactor p A lam (value omega) *
          localFactor q B mu (value omega) =
        divInd D (value omega) *
          (∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
            coefficient lam a * coefficient mu b *
              divInd (p ^ a * q ^ b) (value omega)) := by
    rw [mul_assoc,
      localFactor_mul_eq_product_indicator hpq hp hq]
  simp_rw [hpoint]
  unfold FiniteProbability.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro omega _
  ring

/-- The corresponding exact normalizing denominator. -/
theorem expect_two_restored
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q A B : ℕ} (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    (lam mu : ℝ) :
    nu.expect (fun omega ↦ localFactor p A lam (value omega) *
        localFactor q B mu (value omega)) =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          nu.expect (fun omega ↦
            divInd (p ^ a * q ^ b) (value omega)) := by
  simpa only [divInd, one_dvd, if_pos, one_mul] using
    expect_two_restored_indicator nu value hpq hp hq lam mu
      (A := A) (B := B) (D := 1)

end Probability

end

end Erdos390.Full.LocalFugacityRestoration

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































theorem coefficientTail_nonneg (p A r : ℕ) (eta L : ℝ) :
    0 ≤ coefficientTail p A r eta L := by
  unfold coefficientTail
  positivity











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

/-- The finite local factor at the logarithmic cutoff is literally the
required valuation fugacity. -/
theorem localFactor_valuationCutoff_eq
    {p m M : ℕ} (lam : ℝ) (hp : p.Prime)
    (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p (valuationCutoff p M) lam m =
      lam ^ m.factorization p := by
  exact localFactor_eq_pow_valuation lam hp hm
    (factorization_le_valuationCutoff hp hm hmM)

/-- Exponential form of the exact logarithmically truncated local factor. -/
theorem localFactor_valuationCutoff_exp_eq
    {p m M : ℕ} (eta L : ℝ) (hp : p.Prime)
    (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p (valuationCutoff p M) (Real.exp (eta / L)) m =
      Real.exp (eta / L * valuation p m) := by
  rw [localFactor_valuationCutoff_eq (Real.exp (eta / L)) hp hm hmM]
  rw [valuation, mul_comm, Real.exp_nat_mul]

/-- The natural logarithmic cutoff is no larger than the corresponding real
logarithmic ratio. -/
theorem cast_valuationCutoff_le_log_ratio
    {p M : ℕ} (hp : 1 < p) (hM : 0 < M) :
    (valuationCutoff p M : ℝ) ≤
      Real.log (M : ℝ) / Real.log (p : ℝ) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hpowNat : p ^ valuationCutoff p M ≤ M := by
    exact Nat.pow_log_le_self p hM.ne'
  have hpowPos : (0 : ℝ) < ((p ^ valuationCutoff p M : ℕ) : ℝ) := by
    positivity
  have hpowCast : ((p ^ valuationCutoff p M : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log hpowPos hpowCast
  norm_num only [Nat.cast_pow] at hlog
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ hlogp).2
  simpa [mul_comm] using hlog



end

end Erdos390.Full.ValuationCutoff

end

/- Source module: Erdos390.Full.PaperValuationCutoff -/
section


/-!
# Paper-scale bounds for the logarithmic valuation cutoff

At the physical scale `m ≤ C n` and for `W < p ≤ n^(2/9)`, the exact local
cutoff is `O(L / log W)`.  This turns every restored coefficient tail into
`L⁻¹ p^{-r}` with an exponential constant depending on the already fixed
box and cutoff, while leaving the leading prime-power constant independent
of that box.
-/

open Filter Topology

namespace Erdos390.Full.PaperValuationCutoff

open ArithmeticModel Scale
open ValuationCutoff LocalFugacityBounds

noncomputable section

/-- The logarithmic valuation-cutoff estimate only needs a positive physical
upper endpoint.  The older `1 ≤ C` formulation below is retained as a
compatibility wrapper, but that normalization is not part of the paper's
cell hypotheses. -/
theorem eventually_valuationCutoff_div_L_le_of_pos
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 / Real.log (W : ℝ) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  intro p hpBand
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hpPrime : p.Prime := prime_of_mem_primeBand hpBand
  have hpW : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogWp : Real.log (W : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hW.le)
    exact_mod_cast hpW.le
  have hOneMul : (1 : ℝ) ≤ C * (n : ℝ) := by
    have h := (div_le_iff₀ hC).mp hInvCn
    simpa [mul_comm] using h
  have hphysOne : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast hOneMul
  have hM : 0 < physicalBound C n := lt_of_lt_of_le Nat.zero_lt_one hphysOne
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hM) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hlogPhys0 : 0 ≤ Real.log (physicalBound C n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hphysOne)
  have hcut := cast_valuationCutoff_le_log_ratio hpPrime.one_lt hM
  have hratio :
      Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) := by
    calc
      _ ≤ Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_left hlogPhys0 hlogW hlogWp
      _ ≤ (2 * L n) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_right hlogPhys hlogW.le
  calc
    (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        (Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ)) / L n :=
      div_le_div_of_nonneg_right hcut hL.le
    _ ≤ ((2 * L n) / Real.log (W : ℝ)) / L n :=
      div_le_div_of_nonneg_right hratio hL.le
    _ = 2 / Real.log (W : ℝ) := by
      field_simp [hL.ne', hlogW.ne']







/-- Positive-endpoint version of `eventually_coefficientTail_le`. -/
theorem eventually_coefficientTail_le_of_pos
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ eta : ℝ,
      |eta| ≤ B → ∀ r : ℕ,
      coefficientTail p (valuationCutoff p (physicalBound C n)) r eta (L n) ≤
        ((2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBLEvent : ∀ᶠ n : ℕ in atTop, B ≤ L n :=
    hLTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_valuationCutoff_div_L_le_of_pos C W hC hW,
    hBLEvent, Filter.eventually_gt_atTop 1] with n hcut hBL hn
  intro p hpBand eta heta r
  have hL : 0 < L n := L_pos hn
  have hp2 : 2 ≤ p := (prime_of_mem_primeBand hpBand).two_le
  have hcut' := hcut p hpBand
  have hexponent :
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 * B / Real.log (W : ℝ) := by
    calc
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n =
          B * ((valuationCutoff p (physicalBound C n) : ℝ) / L n) := by
        ring
      _ ≤ B * (2 / Real.log (W : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut' hB
      _ = 2 * B / Real.log (W : ℝ) := by ring
  have hraw := coefficientTail_le (A := valuationCutoff p (physicalBound C n))
    hp2 hB hL hBL heta (r := r)
  have hcoef : 0 ≤ 2 * B / L n := by positivity
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hcoef)
    (by positivity))





end

end Erdos390.Full.PaperValuationCutoff

end

/- Source module: Erdos390.Full.TwoLocalRestoration -/
section


/-!
# Exact restoration of two omitted local primes

The omitted-score marked law is reweighted by the two literal local
valuation fugacities.  This file proves the exact finite identity connecting
that sequential reweighting to the full valuation tilt and then expands both
the marked numerator and the normalizer into prime-power indicators.
-/

open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel FiniteProbability ValuationScoreDomination
open LocalFugacity LocalFugacityRestoration ValuationCutoff

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Two finite probability objects are equal when their mass functions are
equal.  The remaining structure fields are propositions. -/
theorem eq_of_mass_eq (mu nu : FiniteProbability Omega)
    (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk muMass muNonneg muSum =>
      cases nu with
      | mk nuMass nuNonneg nuSum =>
          simp only [FiniteProbability.mk.injEq]
          exact h

/-- Exponential tilting first by `S` and then by `T` is exactly tilting once
by their sum. -/
theorem exponentialTilt_add (mu : FiniteProbability Omega)
    (S T : Omega → ℝ) :
    (mu.exponentialTilt S).exponentialTilt T =
      mu.exponentialTilt (fun omega ↦ S omega + T omega) := by
  apply eq_of_mass_eq
  funext omega
  have hpart :
      (mu.exponentialTilt S).expPartition T =
        mu.expPartition (fun x ↦ S x + T x) / mu.expPartition S := by
    unfold expPartition
    rw [mu.exponentialTilt_expect_eq (fun x ↦ Real.exp (T x)) S]
    congr 1
    unfold expect
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only
    rw [Real.exp_add]
    ring
  change
    (mu.mass omega * Real.exp (S omega) / mu.expPartition S) *
          Real.exp (T omega) /
        (mu.exponentialTilt S).expPartition T =
      mu.mass omega * Real.exp (S omega + T omega) /
        mu.expPartition (fun x ↦ S x + T x)
  rw [hpart]
  rw [Real.exp_add]
  field_simp [ne_of_gt (mu.expPartition_pos S),
    ne_of_gt (mu.expPartition_pos (fun x ↦ S x + T x))]

/-- Sequential-tilt expectation as one exact quotient under the first law. -/
theorem exponentialTilt_add_expect_eq
    (mu : FiniteProbability Omega) (S T A : Omega → ℝ) :
    (mu.exponentialTilt (fun omega ↦ S omega + T omega)).expect A =
      (mu.exponentialTilt S).expect
          (fun omega ↦ A omega * Real.exp (T omega)) /
        (mu.exponentialTilt S).expect (fun omega ↦ Real.exp (T omega)) := by
  rw [← mu.exponentialTilt_add S T]
  rw [(mu.exponentialTilt S).exponentialTilt_expect_eq A T]
  rfl

end FiniteProbability

namespace TwoLocalRestoration



theorem erasePair_subset (P : Finset ℕ) (p q : ℕ) :
    erasePair P p q ⊆ P :=
  (Finset.erase_subset q (P.erase p)).trans (Finset.erase_subset p P)

/-- Literal decomposition of the full valuation score into the omitted
score and two local valuation coordinates. -/
theorem valuationScore_eq_erasePair_add
    (P : Finset ℕ) (eta : ℕ → ℝ) (L : ℝ) {p q m : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q) :
    valuationScore P eta L m =
      valuationScore (erasePair P p q) eta L m +
        (eta p / L) * valuation p m + (eta q / L) * valuation q m := by
  have hqErase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hqP⟩
  unfold valuationScore erasePair
  let f : ℕ → ℝ := fun r ↦ (eta r / L) * valuation r m
  change (∑ r ∈ P, f r) =
    (∑ r ∈ (P.erase p).erase q, f r) + f p + f q
  calc
    (∑ r ∈ P, f r) = (∑ r ∈ P.erase p, f r) + f p :=
      (Finset.sum_erase_add P f hpP).symm
    _ = ((∑ r ∈ (P.erase p).erase q, f r) + f q) + f p := by
      rw [Finset.sum_erase_add (P.erase p) f hqErase]
    _ = (∑ r ∈ (P.erase p).erase q, f r) + f p + f q := by ring

/-- On a bounded positive cell, the two local factors are exactly the
exponential of the omitted local score. -/
theorem twoLocalFactor_valuationCutoff_eq_exp
    {p q m M : ℕ} (eta : ℕ → ℝ) (L : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p (valuationCutoff p M) (Real.exp (eta p / L)) m *
        localFactor q (valuationCutoff q M) (Real.exp (eta q / L)) m =
      Real.exp ((eta p / L) * valuation p m +
        (eta q / L) * valuation q m) := by
  rw [localFactor_valuationCutoff_exp_eq (eta p) L hp hm hmM,
    localFactor_valuationCutoff_exp_eq (eta q) L hq hm hmM,
    ← Real.exp_add]

section Cell

variable {S : Finset ℕ}

/-- Exact two-local restored quotient for the full valuation tilt on an
actual finite set of positive integers with common endpoint `M`. -/
theorem fullTilt_divInd_eq_twoLocal_quotient
    (hS : S.Nonempty) (P : Finset ℕ) (eta : ℕ → ℝ)
    {L : ℝ} {M p q D : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (hp : p.Prime) (hq : q.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    let mu := uniformOnFinset S hS
    let omitted := mu.exponentialTilt
      (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    (mu.exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) =
      omitted.expect (fun m : S ↦
          divInd D m *
            localFactor p (valuationCutoff p M) (Real.exp (eta p / L)) m *
            localFactor q (valuationCutoff q M) (Real.exp (eta q / L)) m) /
        omitted.expect (fun m : S ↦
            localFactor p (valuationCutoff p M) (Real.exp (eta p / L)) m *
            localFactor q (valuationCutoff q M) (Real.exp (eta q / L)) m) := by
  dsimp only
  let mu := uniformOnFinset S hS
  let omitted := mu.exponentialTilt
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
  let localScore : S → ℝ := fun m ↦
    (eta p / L) * valuation p m + (eta q / L) * valuation q m
  have hscore : (fun m : S ↦ valuationScore P eta L m) =
      fun m : S ↦ valuationScore (erasePair P p q) eta L m + localScore m := by
    funext m
    rw [valuationScore_eq_erasePair_add P eta L (m := (m : ℕ))
      hpP hqP hpq]
    dsimp only [localScore]
    ring
  rw [hscore]
  have hadd := mu.exponentialTilt_add_expect_eq
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    localScore (fun m : S ↦ divInd D m)
  rw [hadd]
  congr 1
  · congr 1
    funext m
    rw [← twoLocalFactor_valuationCutoff_eq_exp eta L hp hq
      (hSpos m m.property) (hSle m m.property)]
    ring
  · congr 1
    funext m
    rw [← twoLocalFactor_valuationCutoff_eq_exp eta L hp hq
      (hSpos m m.property) (hSle m m.property)]

/-- The same exact quotient with both local factors expanded into finite
prime-power indicator sums. -/
theorem fullTilt_divInd_eq_twoLocal_indicator_ratio
    (hS : S.Nonempty) (P : Finset ℕ) (eta : ℕ → ℝ)
    {L : ℝ} {M p q D : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (hp : p.Prime) (hq : q.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    let omitted := (uniformOnFinset S hS).exponentialTilt
      (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) =
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦
                divInd D m * divInd (p ^ a * q ^ b) m)) /
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦
                divInd (p ^ a * q ^ b) m)) := by
  dsimp only
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
  rw [fullTilt_divInd_eq_twoLocal_quotient hS P eta hpP hqP hpq hp hq
    hSpos hSle]
  rw [expect_two_restored_indicator omitted (fun m : S ↦ (m : ℕ))
    hpq hp hq, expect_two_restored omitted (fun m : S ↦ (m : ℕ))
    hpq hp hq]

end Cell

end TwoLocalRestoration

end

end Erdos390.Full

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



/-- Every two-prime four-mark modulus is genuinely `yNat`-friable. -/
theorem pairPower_mem_smoothNumbers
    {n W p q a b : ℕ} (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W) :
    pairPower p q a b ∈ Nat.smoothNumbers (yNat n + 1) := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (by
      have := le_yNat_of_mem_primeBand hpBand
      omega)
  have hqSmooth : q ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hq.pos (by
      have := le_yNat_of_mem_primeBand hqBand
      omega)
  exact Nat.mul_mem_smoothNumbers
    (pow_mem_smoothNumbers hpSmooth a) (pow_mem_smoothNumbers hqSmooth b)

/-- A two-prime-power modulus is coprime to every prime left in the score
after erasing its two local primes. -/
theorem pairPower_coprime_erasePair
    {n W p q a b r : ℕ} (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W)
    (hr : r ∈ erasePair (primeBand n W) p q) :
    Nat.Coprime (pairPower p q a b) r := by
  have hrEraseQ := Finset.mem_erase.mp hr
  have hrEraseP := Finset.mem_erase.mp hrEraseQ.2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hrPrime := prime_of_mem_primeBand hrEraseP.2
  have hpr : Nat.Coprime p r :=
    (Nat.coprime_primes hp hrPrime).mpr hrEraseP.1.symm
  have hqr : Nat.Coprime q r :=
    (Nat.coprime_primes hq hrPrime).mpr hrEraseQ.1.symm
  unfold pairPower
  exact (hpr.pow_left a).mul_left (hqr.pow_left b)





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

/-- The paper's exact finite `N_{r,s}/N_{0,0}` identity for an actual
structured-cell law.  All local exponent cutoffs remain literal. -/
theorem fullTilt_pairPower_eq_maxExponent_ratio
    (hS : S.Nonempty) (P : Finset ℕ) (eta : ℕ → ℝ)
    {L : ℝ} {M p q r s : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (hp : p.Prime) (hq : q.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    let omitted := (uniformOnFinset S hS).exponentialTilt
      (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) =
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦
                divInd (pairPower p q (max r a) (max s b)) m)) /
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦ divInd (pairPower p q a b) m)) := by
  dsimp only
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
  rw [fullTilt_divInd_eq_twoLocal_indicator_ratio hS P eta hpP hqP hpq
    hp hq hSpos hSle]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 3
  funext m
  simpa only [pairPower] using
    divInd_pairPower_mul (m := (m : ℕ)) hpq hp hq

end Cell

end

end Erdos390.Full.TwoLocalPairRestoration

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

/-- The partition function of a score bounded in absolute value by `K` is at
least `exp (-K)`. -/
theorem exp_neg_le_expPartition (mu : FiniteProbability Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-K) ≤ mu.expPartition score := by
  unfold expPartition expect
  calc
    Real.exp (-K) = ∑ omega, mu.mass omega * Real.exp (-K) := by
      rw [← Finset.sum_mul, mu.mass_sum, one_mul]
    _ ≤ ∑ omega, mu.mass omega * Real.exp (score omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
      exact Real.exp_le_exp.mpr ((neg_le_neg (hscore omega)).trans
        (neg_abs_le (score omega)))

/-- Pointwise bounded tilting changes any nonnegative expectation by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_expect_le_exp_two_mul
    (mu : FiniteProbability Omega) (A score : Omega → ℝ) (K : ℝ)
    (hA : ∀ omega, 0 ≤ A omega)
    (hscore : ∀ omega, |score omega| ≤ K) :
    (mu.exponentialTilt score).expect A ≤
      Real.exp (2 * K) * mu.expect A := by
  have hZpos : 0 < mu.expPartition score := mu.expPartition_pos score
  have hZlower : Real.exp (-K) ≤ mu.expPartition score :=
    mu.exp_neg_le_expPartition score K hscore
  have hEA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA
  have hnum0 : 0 ≤ mu.expect (fun omega ↦ A omega * Real.exp (score omega)) :=
    mu.expect_nonneg _ fun omega ↦ mul_nonneg (hA omega) (Real.exp_pos _).le
  have hnum : mu.expect (fun omega ↦ A omega * Real.exp (score omega)) ≤
      Real.exp K * mu.expect A := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    calc
      mu.mass omega * (A omega * Real.exp (score omega)) ≤
          mu.mass omega * (A omega * Real.exp K) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        apply mul_le_mul_of_nonneg_left _ (hA omega)
        exact Real.exp_le_exp.mpr ((le_abs_self (score omega)).trans
          (hscore omega))
      _ = Real.exp K * (mu.mass omega * A omega) := by ring
  have hinv : (mu.expPartition score)⁻¹ ≤ Real.exp K := by
    apply (inv_le_iff_one_le_mul₀ hZpos).2
    calc
      1 = Real.exp K * Real.exp (-K) := by
        rw [← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp K * mu.expPartition score :=
        mul_le_mul_of_nonneg_left hZlower (Real.exp_pos K).le
  rw [mu.exponentialTilt_expect_eq A score, div_eq_mul_inv]
  calc
    mu.expect (fun omega ↦ A omega * Real.exp (score omega)) *
        (mu.expPartition score)⁻¹ ≤
      (Real.exp K * mu.expect A) * (mu.expPartition score)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hZpos.le)
    _ ≤ (Real.exp K * mu.expect A) * Real.exp K :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (Real.exp_pos K).le hEA0)
    _ = Real.exp (2 * K) * mu.expect A := by
      rw [show Real.exp (2 * K) = Real.exp K * Real.exp K by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

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

/-- Arbitrary-modulus reciprocal fallback for the genuine omitted valuation
tilt on an actual finite cell.  No smoothness or four-mark condition is
assumed on `D`. -/
theorem omittedValuationTilt_divInd_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D W : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hW : 1 < W) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hpW : ∀ p ∈ P, W ≤ p) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) ≤
      Real.exp (2 * ((B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)))) /
          (c * (D : ℝ)) := by
  let mu := uniformOnFinset S hS
  let K : ℝ := (B / L) *
    (Real.log (M : ℝ) / Real.log (W : ℝ))
  have hscore : ∀ m : S, |valuationScore P eta L m| ≤ K := by
    intro m
    simpa only [K] using abs_valuationScore_le_log_ratio P eta
      (hSpos m m.property) (hSle m m.property) hW hpW hB hL heta
  have htilt := mu.exponentialTilt_expect_le_exp_two_mul
    (fun m : S ↦ divInd D m)
    (fun m : S ↦ valuationScore P eta L m) K
    (fun m ↦ divInd_nonneg D m) hscore
  have hbase : mu.expect (fun m : S ↦ divInd D m) ≤
      1 / (c * (D : ℝ)) := by
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    exact uniformAverage_divInd_le S hD hM hc hcard hSpos hSle
  calc
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) ≤ Real.exp (2 * K) *
            mu.expect (fun m : S ↦ divInd D m) := htilt
    _ ≤ Real.exp (2 * K) * (1 / (c * (D : ℝ))) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (2 * ((B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)))) /
          (c * (D : ℝ)) := by
      dsimp only [K, mu]
      ring

end OmittedTiltFallback

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.TwoLocalRestorationBound -/
section


/-!
# Quantitative error of the exact two-local restoration

This file bounds every nonconstant term in the exact `N_{r,s}` numerator
using the arbitrary-modulus reciprocal fallback.  The result retains the
paper's weighted coefficient tails in both local coordinates; in particular,
it does not replace them by the cardinality of the exponent cutoff.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalRestorationBound

open ArithmeticModel FiniteProbability LocalFugacity LocalFugacityBounds
open OmittedTiltPairChamber

noncomputable section

variable {Omega : Type*} [Fintype Omega]





theorem pairRestorationError_nonneg (p q Ap Aq r s : ℕ)
    (etaP etaQ L G : ℝ) (hG : 0 ≤ G) :
    0 ≤ pairRestorationError p q Ap Aq r s etaP etaQ L G := by
  have hpTail := coefficientTail_nonneg p Ap r etaP L
  have hqTail := coefficientTail_nonneg q Aq s etaQ L
  have hpInv : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hqInv : 0 ≤ 1 / (q : ℝ) ^ s := by positivity
  unfold pairRestorationError
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hG hpTail) hqInv)
      (mul_nonneg (mul_nonneg hG hpInv) hqTail))
    (mul_nonneg (mul_nonneg hG hpTail) hqTail)











/-- The restored normalizer differs from one by the same explicit
coefficient-tail ledger at `(r,s)=(0,0)`. -/
theorem abs_pairRestoredNormalizer_sub_one_le
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q Ap Aq : ℕ} {etaP etaQ L G : ℝ}
    (hprob : ∀ u v : ℕ,
      nu.expect (fun omega ↦ divInd (pairPower p q u v) (value omega)) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v)) :
    |pairRestoredNumerator nu value p q Ap Aq etaP etaQ L 0 0 - 1| ≤
      pairRestorationError p q Ap Aq 0 0 etaP etaQ L G := by
  have h := abs_pairRestoredNumerator_sub_expect_le
    (nu := nu) (value := value) (p := p) (q := q) (Ap := Ap) (Aq := Aq)
    (r := 0) (s := 0) (etaP := etaP) (etaQ := etaQ) (L := L) (G := G)
    hprob
  have hone : nu.expect (fun omega ↦
      divInd (pairPower p q 0 0) (value omega)) = 1 := by
    unfold pairPower divInd FiniteProbability.expect
    simp [nu.mass_sum]
  rwa [hone] at h

/-- Elementary normalized-quotient perturbation with an explicit stable
denominator. -/
theorem abs_div_sub_le_of_abs_den_sub_one_le_half
    {N P D M deltaN deltaP deltaD : ℝ}
    (hdeltaN : 0 ≤ deltaN) (hdeltaP : 0 ≤ deltaP)
    (hdeltaD : 0 ≤ deltaD)
    (hN : |N - P| ≤ deltaN) (hP : |P - M| ≤ deltaP)
    (hD : |D - 1| ≤ deltaD) (hhalf : deltaD ≤ 1 / 2) :
    |N / D - M| ≤ 2 * (deltaN + deltaP + |M| * deltaD) := by
  have hDone : |D - 1| ≤ 1 / 2 := hD.trans hhalf
  have hDpos : 0 < D := by
    have hneg := neg_abs_le (D - 1)
    linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hinv : 1 / D ≤ 2 := by
    apply (div_le_iff₀ hDpos).2
    linarith [neg_abs_le (D - 1)]
  have hnum : |(N - P) + (P - M) + M * (1 - D)| ≤
      deltaN + deltaP + |M| * deltaD := by
    calc
      |(N - P) + (P - M) + M * (1 - D)| ≤
          |N - P| + |P - M| + |M * (1 - D)| := abs_add_three _ _ _
      _ = |N - P| + |P - M| + |M| * |D - 1| := by
        rw [abs_mul]
        congr 2
        exact abs_sub_comm 1 D
      _ ≤ deltaN + deltaP + |M| * deltaD := by
        exact add_le_add_three hN hP
          (mul_le_mul_of_nonneg_left hD (abs_nonneg M))
  have htarget0 : 0 ≤ deltaN + deltaP + |M| * deltaD := by positivity
  have hid : N / D - M = ((N - P) + (P - M) + M * (1 - D)) / D := by
    field_simp [hDne]
    ring
  rw [hid, abs_div, abs_of_pos hDpos]
  calc
    |(N - P) + (P - M) + M * (1 - D)| / D ≤
        (deltaN + deltaP + |M| * deltaD) / D :=
      div_le_div_of_nonneg_right hnum hDpos.le
    _ = (deltaN + deltaP + |M| * deltaD) * (1 / D) := by ring
    _ ≤ (deltaN + deltaP + |M| * deltaD) * 2 :=
      mul_le_mul_of_nonneg_left hinv htarget0
    _ = 2 * (deltaN + deltaP + |M| * deltaD) := by ring

/-- Combining the sharp omitted-law main term with the exact local
restoration gives a normalized full-law approximation.  This theorem is the
finite quotient step; the four-mark module supplies `hmain`, while the
coefficient and tail modules bound the displayed errors. -/
theorem abs_pairRestoredQuotient_sub_main_le
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q Ap Aq r s : ℕ} {etaP etaQ L G main epsilon : ℝ}
    (hprob : ∀ u v : ℕ,
      nu.expect (fun omega ↦ divInd (pairPower p q u v) (value omega)) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v))
    (hG : 0 ≤ G)
    (hmain : |nu.expect (fun omega ↦
        divInd (pairPower p q r s) (value omega)) - main| ≤ epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hhalf : pairRestorationError p q Ap Aq 0 0 etaP etaQ L G ≤ 1 / 2) :
    |pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s /
        pairRestoredNumerator nu value p q Ap Aq etaP etaQ L 0 0 - main| ≤
      2 * (pairRestorationError p q Ap Aq r s etaP etaQ L G + epsilon +
        |main| * pairRestorationError p q Ap Aq 0 0 etaP etaQ L G) := by
  have hrestore := abs_pairRestoredNumerator_sub_expect_le
    (nu := nu) (value := value) (p := p) (q := q) (Ap := Ap) (Aq := Aq)
    (r := r) (s := s) (etaP := etaP) (etaQ := etaQ) (L := L) (G := G)
    hprob
  have hnormalizer := abs_pairRestoredNormalizer_sub_one_le
    (nu := nu) (value := value) (p := p) (q := q) (Ap := Ap) (Aq := Aq)
    (etaP := etaP) (etaQ := etaQ) (L := L) (G := G) hprob
  exact abs_div_sub_le_of_abs_den_sub_one_le_half
    (pairRestorationError_nonneg p q Ap Aq r s etaP etaQ L G hG)
    hepsilon
    (pairRestorationError_nonneg p q Ap Aq 0 0 etaP etaQ L G hG)
    hrestore hmain hnormalizer hhalf

end

end Erdos390.Full.TwoLocalRestorationBound

end

/- Source module: Erdos390.Full.PaperTwoLocalRestorationBound -/
section


/-!
# Paper-scale stability of the two-local normalizer

The exact restoration quotient is useful only after its denominator is shown
uniformly away from zero.  This file performs that quantifier step at the
actual paper scale.  The fallback density-ratio constant is first bounded by
a fixed `B,W,c` ceiling, and the two coefficient tails then tend uniformly to
zero over the moving prime band.
-/

open Filter Topology

namespace Erdos390.Full.PaperTwoLocalRestorationBound

open ArithmeticModel Scale LocalFugacityBounds PaperValuationCutoff
open ValuationCutoff
open TwoLocalRestorationBound

noncomputable section





theorem paperPairFallbackConstant_nonneg (B C c : ℝ) (W n : ℕ)
    (hc : 0 ≤ c) :
    0 ≤ paperPairFallbackConstant B C c W n := by
  unfold paperPairFallbackConstant
  positivity

theorem paperPairFallbackCeiling_pos (B c : ℝ) (W : ℕ) (hc : 0 < c) :
    0 < paperPairFallbackCeiling B c W := by
  unfold paperPairFallbackCeiling
  positivity

/-- The moving physical endpoint contributes no `n`-dependent loss to the
fallback density-ratio constant. -/
theorem eventually_paperPairFallbackConstant_le
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      paperPairFallbackConstant B C c W n ≤
        paperPairFallbackCeiling B c W := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hphysLower : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  have hphysPos : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one hphysLower
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hphysPos) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hK : 2 * ((B / L n) *
      (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) ≤
      4 * B / Real.log (W : ℝ) := by
    calc
      _ ≤ 2 * ((B / L n) *
          ((2 * L n) / Real.log (W : ℝ))) := by gcongr
      _ = 4 * B / Real.log (W : ℝ) := by
        field_simp [hL.ne', hlogW.ne']
        ring
  unfold paperPairFallbackConstant paperPairFallbackCeiling
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hK) hc.le

/-- Uniformly over both moving band primes and all local coefficients in the
fixed box, the actual two-local normalizer error is eventually at most one
half. -/
theorem eventually_pairRestorationError_zero_le_half
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      ∀ etaP etaQ : ℝ, |etaP| ≤ B → |etaQ| ≤ B →
      pairRestorationError p q
        (valuationCutoff p (physicalBound C n))
        (valuationCutoff q (physicalBound C n)) 0 0 etaP etaQ (L n)
        (paperPairFallbackConstant B C c W n) ≤ 1 / 2 := by
  let k : ℕ → ℝ := fun n ↦
    (2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))
  let G0 : ℝ := paperPairFallbackCeiling B c W
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  have hkT : Tendsto k atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦
        (2 * B) * Real.exp (2 * B / Real.log (W : ℝ))) atTop
        (𝓝 ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
      tendsto_const_nhds
    have hmul := hconst.mul hInv
    rw [show k = fun n : ℕ ↦
        ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ))) * (L n)⁻¹ by
      funext n
      dsimp only [k]
      ring]
    simpa using hmul
  have hmajorT : Tendsto (fun n ↦ G0 * (2 * k n + (k n) ^ 2))
      atTop (𝓝 0) := by
    have hpoly : Tendsto (fun n ↦ 2 * k n + (k n) ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hkT).add (hkT.pow 2)
    simpa using tendsto_const_nhds.mul hpoly
  have hmajorHalf : ∀ᶠ n : ℕ in atTop,
      G0 * (2 * k n + (k n) ^ 2) ≤ 1 / 2 :=
    hmajorT (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_paperPairFallbackConstant_le B C c W
      hB hC hc hW,
    eventually_coefficientTail_le_of_pos B C W hB hC hW,
    hmajorHalf, Filter.eventually_gt_atTop 1] with n hG hcoef hhalf hn
  intro p hpBand q hqBand etaP etaQ hetaP hetaQ
  let G := paperPairFallbackConstant B C c W n
  let dp := coefficientTail p (valuationCutoff p (physicalBound C n))
    0 etaP (L n)
  let dq := coefficientTail q (valuationCutoff q (physicalBound C n))
    0 etaQ (L n)
  have hdp0 : 0 ≤ dp := coefficientTail_nonneg _ _ _ _ _
  have hdq0 : 0 ≤ dq := coefficientTail_nonneg _ _ _ _ _
  have hk0 : 0 ≤ k n := by
    dsimp only [k]
    have hL := L_pos hn
    positivity
  have hdp : dp ≤ k n := by
    have h := hcoef p hpBand etaP hetaP 0
    simpa only [dp, k, Nat.cast_zero, zero_add, pow_zero, div_one, mul_one]
      using h
  have hdq : dq ≤ k n := by
    have h := hcoef q hqBand etaQ hetaQ 0
    simpa only [dq, k, Nat.cast_zero, zero_add, pow_zero, div_one, mul_one]
      using h
  have hG0 : 0 ≤ G := paperPairFallbackConstant_nonneg B C c W n hc.le
  have hG00 : 0 ≤ G0 := (paperPairFallbackCeiling_pos B c W hc).le
  have hG' : G ≤ G0 := by simpa only [G, G0] using hG
  have herr : G * dp + G * dq + G * dp * dq ≤ 1 / 2 := by
    calc
      G * dp + G * dq + G * dp * dq ≤
        G0 * dp + G0 * dq + G0 * dp * dq := by
        exact add_le_add_three
          (mul_le_mul_of_nonneg_right hG' hdp0)
          (mul_le_mul_of_nonneg_right hG' hdq0)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hG' hdp0) hdq0)
      _ ≤ G0 * k n + G0 * k n + G0 * (k n) * (k n) := by
        exact add_le_add_three
          (mul_le_mul_of_nonneg_left hdp hG00)
          (mul_le_mul_of_nonneg_left hdq hG00)
          (mul_le_mul
            (mul_le_mul_of_nonneg_left hdp hG00) hdq
            hdq0 (mul_nonneg hG00 hk0))
      _ = G0 * (2 * k n + (k n) ^ 2) := by ring
      _ ≤ 1 / 2 := hhalf
  simpa [pairRestorationError, G, dp, dq] using herr

end

end Erdos390.Full.PaperTwoLocalRestorationBound

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

/- Source module: Erdos390.Full.FullTiltPairHarmonicRate -/
section


/-!
# Harmonic-rate full-tilt pair chamber

This module propagates the definitional omitted-score remainder with
`epsilon n * log (L n) -> 0` through the exact two-local restoration.  The
cutoff is the literal arithmetic chamber `pairPower <= yNat n ^ 4`.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPairHarmonicRate

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination ValuationCutoff
open PaperScaleMarkedCell OmittedTiltPairChamber OmittedTiltFallback
open OmittedTiltHarmonicRate
open TwoLocalRestoration TwoLocalPairRestoration
open TwoLocalRestorationBound PaperTwoLocalRestorationBound
open FullTiltPairChamber

noncomputable section

/-- Actual full-valuation two-prime chamber with a remainder that remains
vanishing after two complete harmonic-row losses. -/
theorem exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto epsilon atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2)
        atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p →
        pairPower p q r s ≤ yNat n ^ 4 →
        Nat.Coprime p H.modulus → Nat.Coprime q H.modulus →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
                (fun m : S ↦ divInd (pairPower p q r s) m) -
              paperDivisibilityMain n (pairPower p q r s)| ≤
            fullPairChamberError H A C B W n p q r s eta epsilon := by
  obtain ⟨K, cOmit, epsilon, hK, hcOmit, hepsilonDef,
      hepsilon0, hepsilonT, hepsilonRate, hepsilonRateSq, Nomit, homit⟩ :=
    exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate
      H hA hAC hC B W hB hW
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let c := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  have hhalfEvent := eventually_pairRestorationError_zero_le_half
    B C c W hB hC hc hW
  obtain ⟨Nhalf, hhalf⟩ := Filter.eventually_atTop.mp hhalfEvent
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hphysEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ physicalBound C n := by
    filter_upwards [hcastTop.eventually (eventually_ge_atTop (1 / C))]
      with n hInvCn
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  obtain ⟨Nphys, hphys⟩ := Filter.eventually_atTop.mp hphysEvent
  let N₀ := max Nomit (max Ndensity (max Nhalf (max Nphys 2)))
  refine ⟨epsilon, hepsilon0, hepsilonT, hepsilonRate, hepsilonRateSq,
    N₀, ?_⟩
  intro n p q r s eta hN hpBand hqErase hD4 hpHead hqHead heta
  have hNomit : Nomit ≤ n := by dsimp only [N₀] at hN; omega
  have hNdensity : Ndensity ≤ n := by dsimp only [N₀] at hN; omega
  have hNhalf : Nhalf ≤ n := by dsimp only [N₀] at hN; omega
  have hNphys : Nphys ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  have hqData := Finset.mem_erase.mp hqErase
  have hpq : p ≠ q := hqData.1.symm
  have hqBand : q ∈ primeBand n W := hqData.2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hDsmooth : pairPower p q r s ∈
      Nat.smoothNumbers (yNat n + 1) :=
    pairPower_mem_smoothNumbers hpBand hqBand
  have hDhead : Nat.Coprime (pairPower p q r s) H.modulus := by
    unfold pairPower
    exact (hpHead.pow_left r).mul_left (hqHead.pow_left s)
  let P := erasePair (primeBand n W) p q
  have hPsub : P ⊆ primeBand n W :=
    erasePair_subset (primeBand n W) p q
  have hDcop : ∀ u ∈ P, Nat.Coprime (pairPower p q r s) u := by
    intro u hu
    exact pairPower_coprime_erasePair hpBand hqBand hu
  have hetaP : ∀ u ∈ P, |eta u| ≤ B := by
    intro u hu
    exact heta u (hPsub hu)
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  have hpairData := homit (P := P) eta hNomit hDpos hD4 hDsmooth
    hDhead hPsub hDcop hetaP
  change S.Nonempty ∧ ∀ hS : S.Nonempty,
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta (L n) m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) -
        paperDivisibilityMain n (pairPower p q r s)| ≤
      epsilon n / (pairPower p q r s : ℝ) at hpairData
  obtain ⟨hSnonempty, hmainAll⟩ := hpairData
  refine ⟨hSnonempty, ?_⟩
  intro hS
  have hcellDensity := hdensity hNdensity
  have hCpos : 0 < C := hC
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hMpos : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one (hphys n hNphys)
  have hMcast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hcard : c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (physicalBound C n : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hCpos.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S] using hcellDensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore P eta (L n) m)
  let G := paperPairFallbackConstant B C c W n
  have hpW : ∀ z ∈ P, W ≤ z := by
    intro z hz
    exact (cutoff_lt_of_mem_primeBand (hPsub hz)).le
  have hprob : ∀ u v : ℕ,
      omitted.expect (fun m : S ↦ divInd (pairPower p q u v) m) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v) := by
    intro u v
    have hPairPos : 0 < pairPower p q u v := pairPower_pos hp hq
    have hraw := omittedValuationTilt_divInd_le S P hS eta hPairPos hMpos
      hB (L_pos hn) hW hc hcard hSpos hSle hpW hetaP
    simpa only [omitted, G, paperPairFallbackConstant, P, pairPower,
      Nat.cast_mul, Nat.cast_pow, div_div] using hraw
  have hG : 0 ≤ G := paperPairFallbackConstant_nonneg B C c W n hc.le
  have hnormalizer := hhalf n hNhalf p hpBand q hqBand (eta p) (eta q)
    (heta p hpBand) (heta q hqBand)
  have hmain := hmainAll hS
  have hquot := abs_pairRestoredQuotient_sub_main_le
    (nu := omitted) (value := fun m : S ↦ (m : ℕ))
    (p := p) (q := q)
    (Ap := valuationCutoff p (physicalBound C n))
    (Aq := valuationCutoff q (physicalBound C n))
    (r := r) (s := s) (etaP := eta p) (etaQ := eta q)
    (L := L n) (G := G)
    (main := paperDivisibilityMain n (pairPower p q r s))
    (epsilon := epsilon n / (pairPower p q r s : ℝ))
    hprob hG hmain (div_nonneg (hepsilon0 n) (by positivity)) hnormalizer
  have hexact := fullTilt_pairPower_eq_maxExponent_ratio hS
    (primeBand n W) eta hpBand hqBand hpq hp hq hSpos hSle
    (L := L n) (M := physicalBound C n) (r := r) (s := s)
  have hexact' :
      ((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) =
        pairRestoredNumerator omitted (fun m : S ↦ (m : ℕ)) p q
            (valuationCutoff p (physicalBound C n))
            (valuationCutoff q (physicalBound C n))
            (eta p) (eta q) (L n) r s /
          pairRestoredNumerator omitted (fun m : S ↦ (m : ℕ)) p q
            (valuationCutoff p (physicalBound C n))
            (valuationCutoff q (physicalBound C n))
            (eta p) (eta q) (L n) 0 0 := by
    simpa only [pairRestoredNumerator, omitted, P] using hexact
  rw [hexact']
  simpa only [fullPairChamberError, c, G] using hquot

end

end Erdos390.Full.FullTiltPairHarmonicRate

end

theorem solution : Erdos390.RemainingAnalyticGoal001_004 := by
  exact @Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
