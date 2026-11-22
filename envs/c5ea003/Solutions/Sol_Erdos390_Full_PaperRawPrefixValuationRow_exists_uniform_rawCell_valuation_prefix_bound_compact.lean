-- Prove2me | solution 1 for Erdos390.Full.PaperRawPrefixValuationRow.exists_uniform_rawCell_valuation_prefix_bound_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:17:03.487402+00:00
-- url     : https://prove2.me/submissions/67f65d2b-18b4-491b-b256-baf342290dbf

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
import Theorems.Thm_Erdos390_Full_PaperMovingPrefixMarkedCell_exists_uniform_movingPrefix_divInd_centered_bound_compact
import Theorems.Thm_Erdos390_Full_PaperMovingPrefixMarkedCell_exists_uniform_movingPrefix_uniformAverage_divInd_bound
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound


section
theorem Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_centered_bound : Erdos390.RemainingAnalyticGoal004_005 := @Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_centered_bound_compact
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



theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
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

























end BoundedValuationLaw

end PrimePowerCovariance

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













end

end Erdos390.Full.PaperValuationCutoff

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









lemma card_highExponents_le (A : ℕ) : (highExponents A).card ≤ A := by
  simp [highExponents]







lemma card_diagonalBeyondFour_le (n p A : ℕ) :
    (diagonalBeyondFour n p A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)























/-- A diagonal exponent beyond four marks has two complete extra factors
of `yNat` after the first two powers of `p`. -/
lemma yNat_sq_lt_pow_sub_two_of_diagonalBeyondFour
    {n p A r : ℕ} (hr : r ∈ diagonalBeyondFour n p A)
    (hpY : p ≤ yNat n) : yNat n ^ 2 < p ^ (r - 2) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hfour : yNat n ^ 4 < p ^ r := (Finset.mem_filter.mp hr).2
  by_contra hnot
  have hexcess : p ^ (r - 2) ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hfactor : p ^ r = p ^ 2 * p ^ (r - 2) := by
    calc
      p ^ r = p ^ (2 + (r - 2)) := by
        congr 1
        omega
      _ = p ^ 2 * p ^ (r - 2) := pow_add _ _ _
  have hupper : p ^ r ≤ yNat n ^ 4 := by
    calc
      p ^ r = p ^ 2 * p ^ (r - 2) := hfactor
      _ ≤ yNat n ^ 2 * yNat n ^ 2 := Nat.mul_le_mul hp2 hexcess
      _ = yNat n ^ 4 := by ring
  omega

/-- Complete diagonal reciprocal tail with the exact `(2r-3)` weight. -/
theorem sum_diagonalBeyondFour_weighted_reciprocal_le
    {n p A : ℕ} (hp0 : 0 < p) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) :
    (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      (2 * (A : ℝ) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  let K : ℝ := (2 * (A : ℝ)) /
    ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)
  have hpoint (r : ℕ) (hr : r ∈ diagonalBeyondFour n p A) :
      ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r ≤ K := by
    have hrmem : r ∈ highExponents A := (Finset.mem_filter.mp hr).1
    have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
    have hrA : r ≤ A := (mem_highExponents.mp hrmem).2
    have hexcess := yNat_sq_lt_pow_sub_two_of_diagonalBeyondFour hr hpY
    have hfactor : (p : ℝ) ^ r =
        (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
      calc
        (p : ℝ) ^ r = (p : ℝ) ^ (2 + (r - 2)) := by
          congr 1
          omega
        _ = (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := pow_add _ _ _
    have hrecip : 1 / (p : ℝ) ^ r ≤
        1 / ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hfactor]
      gcongr
      exact_mod_cast hexcess.le
    have hweight : ((2 * r - 3 : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      exact_mod_cast (show 2 * r - 3 ≤ 2 * A by omega)
    have hrecip' : ((p : ℝ) ^ r)⁻¹ ≤
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)⁻¹ := by
      simpa [one_div] using hrecip
    dsimp [K]
    rw [div_eq_mul_inv]
    exact mul_le_mul hweight hrecip' (by positivity) (by positivity)
  calc
    (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
        ∑ _r ∈ diagonalBeyondFour n p A, K := by
      apply Finset.sum_le_sum
      intro r hr
      exact hpoint r hr
    _ = ((diagonalBeyondFour n p A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_diagonalBeyondFour_le n p A
    _ = (2 * (A : ℝ) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      simp [K, div_eq_mul_inv]
      ring

/-! ## Literal endpoint multiplicities -/







/-! ## Actual logarithmic cutoffs and paper-scale ledgers -/







/-- The already-proved valuation-cutoff estimate in the multiplication form
used by every finite tail and endpoint ledger below. -/
theorem eventually_actualExponentCutoff_cast_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (actualExponentCutoff C n p : ℝ) ≤ cutoffScale W * L n := by
  filter_upwards [eventually_valuationCutoff_div_L_le_of_pos C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp
  have hL : 0 < L n := L_pos hn
  have hpCut := hcut p hp
  unfold actualExponentCutoff cutoffScale
  exact (div_le_iff₀ hL).mp hpCut

private lemma band_prime_data {n W p : ℕ} (hp : p ∈ primeBand n W) :
    0 < p ∧ 0 < yNat n ∧ p ≤ yNat n := by
  have hp0 : 0 < p := (prime_of_mem_primeBand hp).pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
  exact ⟨hp0, hp0.trans_le hpY, hpY⟩







/-- Paper-scale weighted diagonal reciprocal tail. -/
theorem eventually_actual_diagonal_weighted_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ diagonalBeyondFour n p (actualExponentCutoff C n p),
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
        (2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    (show 0 ≤ (actualExponentCutoff C n p : ℝ) by positivity).trans
      (hcut p hp)
  have hsq : (actualExponentCutoff C n p : ℝ) ^ 2 ≤
      (cutoffScale W * L n) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hscale0).2 (hcut p hp)
  apply (sum_diagonalBeyondFour_weighted_reciprocal_le hp0 hY0 hpY).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith







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











end

end Erdos390.Full.PrimePowerCutoffCovariance

end

/- Source module: Erdos390.Full.PaperPrimePowerAuxiliaryPrime -/
section


/-!
# A uniform auxiliary prime for diagonal restoration

The diagonal probability is recovered from the two-local restoration by
giving each row prime a distinct auxiliary band prime with exponent zero.
Two fixed primes above the cutoff suffice once the moving band reaches them.
-/

open Filter

namespace Erdos390.Full.PaperPrimePowerAuxiliaryPrime

open ArithmeticModel HeadPattern

noncomputable section



/-- Every prime in the moving band is coprime to the head modulus as soon as
all primes occurring in the head pattern lie at or below the cutoff.  Unlike
`H.modulus ≤ W`, this is compatible with prescribing every prime `q ≤ W`. -/
theorem coprime_modulus_of_mem_primeBand_of_headSupport
    (H : Pattern) {n W p : ℕ}
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hpBand : p ∈ primeBand n W) : Nat.Coprime p H.modulus := by
  rw [Pattern.modulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hp := prime_of_mem_primeBand hpBand
  have hqPrime := H.prime_mem q hq
  have hpGt : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact (Nat.not_lt_of_ge (hHeadLe p hq)) hpGt
  exact (Nat.coprime_primes hp hqPrime).mpr hpq





end

end Erdos390.Full.PaperPrimePowerAuxiliaryPrime

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































/-- Absolute expectation is bounded by expectation of the pointwise
absolute value. -/
theorem abs_expect_le_expect_abs
    (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    |mu.expect F| ≤ mu.expect (fun omega ↦ |F omega|) := by
  unfold expect
  calc
    |∑ omega, mu.mass omega * F omega| ≤
        ∑ omega, |mu.mass omega * F omega| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ omega, mu.mass omega * |F omega| := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg omega)]











/-- Covariance is controlled by one marked absolute first moment and the
two marginal absolute first moments. -/
theorem abs_covariance_le_expect_abs_mul_add
    (mu : FiniteProbability Omega) (F S : Omega → ℝ) :
    |mu.covariance F S| ≤
      mu.expect (fun omega ↦ |F omega| * |S omega|) +
        mu.expect (fun omega ↦ |F omega|) *
          mu.expect (fun omega ↦ |S omega|) := by
  unfold covariance
  calc
    |mu.expect (fun omega ↦ F omega * S omega) -
        mu.expect F * mu.expect S| ≤
      |mu.expect (fun omega ↦ F omega * S omega)| +
        |mu.expect F * mu.expect S| := abs_sub _ _
    _ ≤ mu.expect (fun omega ↦ |F omega * S omega|) +
        (mu.expect (fun omega ↦ |F omega|) *
          mu.expect (fun omega ↦ |S omega|)) := by
      exact add_le_add (mu.abs_expect_le_expect_abs _)
        (by
          rw [abs_mul]
          exact mul_le_mul (mu.abs_expect_le_expect_abs F)
            (mu.abs_expect_le_expect_abs S) (abs_nonneg _)
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _))
    _ = mu.expect (fun omega ↦ |F omega| * |S omega|) +
        mu.expect (fun omega ↦ |F omega|) *
          mu.expect (fun omega ↦ |S omega|) := by
      congr 2
      funext omega
      exact abs_mul _ _













end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry















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

/- Source module: Erdos390.Full.PaperMovingPrefixMarkedCell -/
section


/-!
# Uniform moving-prefix endpoint bookkeeping

For a prefix endpoint `k` inside a fixed physical interval, put
`D = k / n`.  Then `physicalBound D n = k` exactly.  Moreover `D` stays
in the original fixed compact physical interval.  These elementary facts
allow the marked-cell endpoint theorem to be applied without pretending
that the moving endpoint is fixed as `n` varies.
-/

namespace Erdos390.Full.PaperMovingPrefixMarkedCell

open ArithmeticModel PaperScaleMarkedCell
open HeadPattern StructuredCells MarkedFriableAsymptotic
open StructuredCellAsymptotic
open scoped BigOperators

noncomputable section



























/-! ## Exact prefix normalization identities -/





/-- Exact identification of the centered counting expression with the
finite-probability covariance used by the bridge. -/
theorem uniformOnFinset_covariance_divInd_prefix_eq
    (S : Finset ℕ) (hS : S.Nonempty) (d k : ℕ) :
    (FiniteProbability.uniformOnFinset S hS).covariance
        (fun m : S ↦ divInd d (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0) =
      DivisibilityMomentBounds.uniformAverage S
          (fun m ↦ divInd d m * if m ≤ k then 1 else 0) -
        DivisibilityMomentBounds.uniformAverage S (divInd d) *
          DivisibilityMomentBounds.uniformAverage S
            (fun m ↦ if m ≤ k then 1 else 0) := by
  unfold FiniteProbability.covariance
  rw [FiniteProbability.uniformOnFinset_expect_eq,
    FiniteProbability.uniformOnFinset_expect_eq,
    FiniteProbability.uniformOnFinset_expect_eq]
  rw [show
    (∑ x : S, divInd d (x : ℕ) *
        if (x : ℕ) ≤ k then (1 : ℝ) else 0) =
      ∑ m ∈ S, divInd d m * if m ≤ k then (1 : ℝ) else 0 by
        simpa only using FiniteProbability.sum_subtype_eq_sum_filter S
          (fun m : ℕ ↦ divInd d m * if m ≤ k then (1 : ℝ) else 0)]
  rw [show (∑ x : S, divInd d (x : ℕ)) =
      ∑ m ∈ S, divInd d m by
        simpa only using FiniteProbability.sum_subtype_eq_sum_filter S
          (fun m : ℕ ↦ divInd d m)]
  rw [show (∑ x : S, if (x : ℕ) ≤ k then (1 : ℝ) else 0) =
      ∑ m ∈ S, if m ≤ k then (1 : ℝ) else 0 by
        simpa only using FiniteProbability.sum_subtype_eq_sum_filter S
          (fun m : ℕ ↦ if m ≤ k then (1 : ℝ) else 0)]
  unfold DivisibilityMomentBounds.uniformAverage
  rfl













/-- Finite-probability form of the preceding centered estimate, with the
actual nonemptiness witness returned explicitly. -/
theorem exists_uniform_movingPrefix_divInd_covariance_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      let S := structuredCell P (physicalBound A n)
        (physicalBound C n) (yNat n)
      ∃ hS : S.Nonempty,
        |(FiniteProbability.uniformOnFinset S hS).covariance
            (fun m : S ↦ divInd d (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
          K / ((d : ℝ) * Scale.L n) := by
  obtain ⟨K, hK, Nc, hc⟩ :=
    exists_uniform_movingPrefix_divInd_centered_bound P hA hAC
  obtain ⟨Kj, hKj, Nj, hj⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  refine ⟨K, hK, max Nc Nj, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  dsimp only
  have hNc : Nc ≤ n := by omega
  have hNj : Nj ≤ n := by omega
  have hjoint := hj hNj hlow hhigh hd hd4 hdsmooth hcop
  let S : Finset ℕ := structuredCell P (physicalBound A n)
    (physicalBound C n) (yNat n)
  have hS : S.Nonempty := by simpa only [S] using hjoint.1
  refine ⟨hS, ?_⟩
  rw [uniformOnFinset_covariance_divInd_prefix_eq]
  simpa only [S] using hc hNc hlow hhigh hd hd4 hdsmooth hcop

end

end Erdos390.Full.PaperMovingPrefixMarkedCell

end

/- Source module: Erdos390.Full.PaperRawPrefixThirdCumulantFallback -/
section


/-!
# Raw-cell fallback for the moving-prefix third cumulant

The sharp four-mark estimate is used only when the relevant lcm lies in the
friable chamber.  Outside that chamber the proof needs a completely uniform
reciprocal fallback.  This file supplies that fallback directly for the
un-tilted counting law on an actual structured cell.

There are two logically separate ingredients.

* A finite-probability lemma shows that reciprocal divisor expectations imply
  a reciprocal divisor/prefix covariance and then an lcm-scale third-cumulant
  bound.  No asymptotic statement or independence assertion is used.
* The positive density theorem for a structured cell supplies the reciprocal
  divisor expectations with a constant depending only on the fixed cell.

The displayed constants are deliberately retained: for coprime `D,E` the
third cumulant is bounded by `(2G+4G^2)/(DE)`, which is exactly the coefficient
used by the beyond-four prime-power ledger after setting its fallback
parameter to `2G`.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open DivisibilityMomentBounds
open FiniteProbability
open PaperScaleMarkedCell
open FullTiltPairChamber

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- If every divisor event has expectation at most `G/D`, its covariance
with an arbitrary `[0,1]`-valued prefix statistic is at most `2G/D`.

The harmless factor two comes from bounding the joint and product terms
separately.  Keeping this elementary form avoids any hidden use of positive
association or independence. -/
theorem abs_covariance_divInd_prefix_le_of_reciprocal_expectation
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D : ℕ} {G : ℝ}
    (hD : 0 < D)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : mu.expect (fun omega ↦ divInd D (value omega)) ≤
      G / (D : ℝ)) :
    |mu.covariance (fun omega ↦ divInd D (value omega)) pref| ≤
      2 * G / (D : ℝ) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hFabs :
      (fun omega ↦ |divInd D (value omega)|) =
        fun omega ↦ divInd D (value omega) := by
    funext omega
    rw [abs_of_nonneg (divInd_nonneg D (value omega))]
  have hPabs : (fun omega ↦ |pref omega|) = pref := by
    funext omega
    rw [abs_of_nonneg (hpref0 omega)]
  have hmarked :
      mu.expect (fun omega ↦
          |divInd D (value omega)| * |pref omega|) ≤
        mu.expect (fun omega ↦ divInd D (value omega)) := by
    apply mu.expect_mono
    intro omega
    rw [abs_of_nonneg (divInd_nonneg D (value omega)),
      abs_of_nonneg (hpref0 omega)]
    exact mul_le_of_le_one_right (divInd_nonneg D (value omega))
      (hpref1 omega)
  have hprefMean : mu.expect (fun omega ↦ |pref omega|) ≤ 1 := by
    rw [hPabs]
    calc
      mu.expect pref ≤ mu.expect (fun _ ↦ (1 : ℝ)) :=
        mu.expect_mono pref _ hpref1
      _ = 1 := by
        unfold expect
        rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hFmean0 : 0 ≤
      mu.expect (fun omega ↦ divInd D (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg D (value omega))
  have hraw := mu.abs_covariance_le_expect_abs_mul_add
    (fun omega ↦ divInd D (value omega)) pref
  rw [hFabs] at hraw
  calc
    |mu.covariance (fun omega ↦ divInd D (value omega)) pref| ≤
        mu.expect (fun omega ↦
            |divInd D (value omega)| * |pref omega|) +
          mu.expect (fun omega ↦ divInd D (value omega)) *
            mu.expect (fun omega ↦ |pref omega|) := hraw
    _ ≤ mu.expect (fun omega ↦ divInd D (value omega)) +
          mu.expect (fun omega ↦ divInd D (value omega)) * 1 := by
      exact add_le_add hmarked
        (mul_le_mul_of_nonneg_left hprefMean hFmean0)
    _ ≤ G / (D : ℝ) + G / (D : ℝ) := by
      exact add_le_add hdiv (by simpa using hdiv)
    _ = 2 * G / (D : ℝ) := by ring





end FiniteProbability

namespace PaperRawPrefixThirdCumulantFallback

/-- The un-tilted law on a fixed structured cell has a reciprocal divisor
bound uniform in the divisor and in all sufficiently large `n`. -/
theorem exists_uniform_rawCell_divInd_fallback
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (uniformOnFinset S hS).expect
            (fun m : S ↦ divInd D (m : ℕ)) ≤ G / (D : ℝ) := by
  let c : ℝ := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  let G : ℝ := 1 / c
  have hG : 0 < G := one_div_pos.mpr hc
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  have hphysEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ physicalBound C n := by
    have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hcastTop.eventually
      (eventually_ge_atTop (1 / C))] with n hn
    unfold physicalBound
    apply Nat.le_floor
    have := (div_le_iff₀ hC).mp hn
    exact_mod_cast (show (1 : ℝ) ≤ C * (n : ℝ) by
      simpa [mul_comm] using this)
  obtain ⟨Nphys, hphys⟩ := Filter.eventually_atTop.mp hphysEvent
  refine ⟨G, hG, max 2 (max Ndensity Nphys), ?_⟩
  intro n hN
  have hn : 1 < n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNphys : Nphys ≤ n := by omega
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  change ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
    (uniformOnFinset S hS).expect
        (fun m : S ↦ divInd D (m : ℕ)) ≤ G / (D : ℝ)
  intro hS D hD
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hMpos : 0 < physicalBound C n :=
    Nat.zero_lt_of_lt (hphys n hNphys)
  have hMcast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le hnR.le)
  have hcard : c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (physicalBound C n : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hC.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S] using hdensity hNdensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  rw [Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage]
  have hraw := OmittedTiltFallback.uniformAverage_divInd_le S hD hMpos hc
    hcard hSpos hSle
  calc
    DivisibilityMomentBounds.uniformAverage S (divInd D) ≤
        1 / (c * (D : ℝ)) := hraw
    _ = G / (D : ℝ) := by
      dsimp only [G]
      ring







end PaperRawPrefixThirdCumulantFallback

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







/-- On one raw structured cell, the genuine full valuation has a uniformly
small covariance with every moving physical prefix.  The second displayed
term is the exact beyond-four contribution; no infinite prime-power series
or asymptotic `O`-notation is hidden in the statement. -/
theorem exists_uniform_rawCell_valuation_prefix_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k p : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      p ∈ primeBand n W →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covariance
            (fun m : S ↦ valuation p (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
          (2 * K / L n) * (1 / (p : ℝ)) +
            (4 * G * (cutoffScale W * L n) ^ 2) /
              ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  obtain ⟨K, hK, Nmove, hmove⟩ :=
    PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_covariance_bound
      H hA hAC
  obtain ⟨G, hG, Ndiv, hdiv⟩ :=
    PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_divInd_fallback
      H hA hAC hC
  have htailEvent := eventually_actual_diagonal_weighted_reciprocal_tail_le
    C W hC hW
  obtain ⟨Ntail, htail⟩ := Filter.eventually_atTop.mp htailEvent
  refine ⟨K, hK, G, hG, max 2 (max Nmove (max Ndiv Ntail)), ?_⟩
  intro n k p hN hlow hhigh hpBand
  have hn : 1 < n := by omega
  have hNmove : Nmove ≤ n := by omega
  have hNdiv : Ndiv ≤ n := by omega
  have hNtail : Ntail ≤ n := by omega
  have hp := prime_of_mem_primeBand hpBand
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hY2 : 2 ≤ yNat n := hp.two_le.trans hpY
  have hp4 : p ≤ yNat n ^ 4 := hpY.trans (Nat.le_pow (by omega : 0 < 4))
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (Nat.lt_succ_of_le hpY)
  have hpHead : Nat.Coprime p H.modulus :=
    PaperPrimePowerAuxiliaryPrime.coprime_modulus_of_mem_primeBand_of_headSupport
      H hHeadLe hpBand
  let M := physicalBound C n
  let R := actualExponentCutoff C n p
  let S := structuredCell H (physicalBound A n) M (yNat n)
  change ∀ hS : S.Nonempty,
    |(uniformOnFinset S hS).covariance
        (fun m : S ↦ valuation p (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤ _
  intro hS
  let mu := uniformOnFinset S hS
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  let law : BoundedValuationLaw S M :=
    StructuredCellValuationLaw.ofProbability H (physicalBound A n) M
      (yNat n) mu
  have hdecomp :
      (fun m : S ↦ valuation p (m : ℕ)) =
        fun m : S ↦ divInd p (m : ℕ) +
          ∑ r ∈ highExponents R, divInd (p ^ r) (m : ℕ) := by
    funext m
    change law.V p m = law.I p m +
      ∑ r ∈ highExponents R, law.Ip p r m
    rw [law.V_eq_I_add_J,
      PrimePowerCutoffCovariance.J_eq_valuationCutoff_sum law hp]
    rfl
  have hpref0 : ∀ m : S, 0 ≤ pref m := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hpref1 : ∀ m : S, pref m ≤ 1 := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hsharp (r : ℕ) (hr : 1 ≤ r) (hr4 : p ^ r ≤ yNat n ^ 4) :
      |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| ≤
        K / (((p ^ r : ℕ) : ℝ) * L n) := by
    have hpowSmooth := StructuredCells.pow_mem_smoothNumbers hpSmooth r
    have hpowHead := hpHead.pow_left r
    obtain ⟨hS', hraw⟩ := hmove hNmove hlow hhigh
      (pow_pos hp.pos r) hr4 hpowSmooth hpowHead
    simpa only [S, M, mu, pref] using hraw
  have hfallback (r : ℕ) (hr : 1 ≤ r) :
      |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| ≤
        2 * G / ((p ^ r : ℕ) : ℝ) := by
    have hdivPow :
        mu.expect (fun m : S ↦ divInd (p ^ r) (m : ℕ)) ≤
          G / ((p ^ r : ℕ) : ℝ) := by
      simpa only [S, M, mu] using
        hdiv hNdiv hS (p ^ r) (pow_pos hp.pos r)
    exact mu.abs_covariance_divInd_prefix_le_of_reciprocal_expectation
      (fun m : S ↦ (m : ℕ)) pref (pow_pos hp.pos r)
      hpref0 hpref1 hdivPow
  let inside := (highExponents R).filter (fun r ↦ p ^ r ≤ yNat n ^ 4)
  let outside := (highExponents R).filter (fun r ↦ ¬p ^ r ≤ yNat n ^ 4)
  have hsplit (F : ℕ → ℝ) :
      (∑ r ∈ highExponents R, F r) =
        (∑ r ∈ inside, F r) + ∑ r ∈ outside, F r := by
    dsimp only [inside, outside]
    exact (Finset.sum_filter_add_sum_filter_not
      (highExponents R) (fun r ↦ p ^ r ≤ yNat n ^ 4) F).symm
  have hfirst :
      |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref| ≤
        K / ((p : ℝ) * L n) := by
    simpa only [pow_one, Nat.cast_pow] using
      hsharp 1 (by omega) (by simpa using hp4)
  have hins :
      (∑ r ∈ inside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        ∑ r ∈ inside, K / (((p ^ r : ℕ) : ℝ) * L n) := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact hsharp r ((show 1 ≤ 2 by omega).trans
      (mem_highExponents.mp hr'.1).1) hr'.2
  have hinsReciprocal :
      (∑ r ∈ inside, 1 / ((p ^ r : ℕ) : ℝ)) ≤
        2 / (p : ℝ) ^ 2 := by
    calc
      (∑ r ∈ inside, 1 / ((p ^ r : ℕ) : ℝ)) ≤
          ∑ r ∈ highExponents R, 1 / ((p ^ r : ℕ) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro r hr _
        positivity
      _ ≤ 2 / (p : ℝ) ^ 2 := by
        simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1) (A := R) hp.two_le)
  have hinsBound :
      (∑ r ∈ inside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        (K / L n) * (2 / (p : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ r ∈ inside,
          K / (((p ^ r : ℕ) : ℝ) * L n) := hins
      _ = (K / L n) *
          (∑ r ∈ inside, 1 / ((p ^ r : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ ≤ (K / L n) * (2 / (p : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinsReciprocal
          (div_nonneg hK.le (L_pos hn).le)
  have houtEq : outside = diagonalBeyondFour n p R := by
    ext r
    simp only [outside, diagonalBeyondFour, Finset.mem_filter, Nat.not_le]
  have hout :
      (∑ r ∈ outside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        2 * G *
          (∑ r ∈ diagonalBeyondFour n p R,
            ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
    rw [houtEq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hrHigh := (Finset.mem_filter.mp hr).1
    have hr2 := (mem_highExponents.mp hrHigh).1
    have hfb := hfallback r (by omega)
    have hweight : (1 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * r - 3 by omega)
    have hpPow : (0 : ℝ) < (p : ℝ) ^ r := by
      exact pow_pos (by exact_mod_cast hp.pos) r
    calc
      _ ≤ 2 * G / ((p ^ r : ℕ) : ℝ) := hfb
      _ = 2 * G * (1 / (p : ℝ) ^ r) := by
        norm_cast
        rw [Nat.cast_pow]
        ring
      _ ≤ 2 * G *
          (((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hG.le)
        exact div_le_div_of_nonneg_right hweight hpPow.le
  have houtBound :
      (∑ r ∈ outside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) ≤
        (4 * G * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
    calc
      _ ≤ 2 * G *
          (∑ r ∈ diagonalBeyondFour n p R,
            ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := hout
      _ ≤ 2 * G *
          ((2 * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [R] using htail n hNtail p hpBand)
          (mul_nonneg (by norm_num) hG.le)
      _ = (4 * G * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by ring
  rw [hdecomp, mu.covariance_add_left, mu.covariance_sum_left]
  calc
    |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref +
        ∑ r ∈ highExponents R,
          mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| ≤
      |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref| +
        ∑ r ∈ highExponents R,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref| := by
      exact (abs_add_le _ _).trans
        (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ = |mu.covariance (fun m : S ↦ divInd p (m : ℕ)) pref| +
        ((∑ r ∈ inside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) +
        ∑ r ∈ outside,
          |mu.covariance (fun m : S ↦ divInd (p ^ r) (m : ℕ)) pref|) := by
      rw [hsplit]
    _ ≤ K / ((p : ℝ) * L n) +
        ((K / L n) * (2 / (p : ℝ) ^ 2) +
          (4 * G * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) :=
      add_le_add hfirst (add_le_add hinsBound houtBound)
    _ ≤ (2 * K / L n) * (1 / (p : ℝ)) +
        (4 * G * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hpR0 : (0 : ℝ) < p := by positivity
      have hL : 0 < L n := L_pos hn
      have hmain : K / ((p : ℝ) * L n) +
          (K / L n) * (2 / (p : ℝ) ^ 2) ≤
          (2 * K / L n) * (1 / (p : ℝ)) := by
        field_simp [hpR0.ne', hL.ne']
        nlinarith [hK]
      linarith

end PaperRawPrefixValuationRow

end

end Erdos390.Full

end

theorem solution : Erdos390.RemainingAnalyticGoal004_006 := by
  exact @Erdos390.Full.PaperRawPrefixValuationRow.exists_uniform_rawCell_valuation_prefix_bound
