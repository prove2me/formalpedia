-- Prove2me | solution 1 for Erdos390.Full.OmittedTiltHarmonicRate.exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:02:25.794342+00:00
-- url     : https://prove2.me/submissions/301c8577-d2c4-4833-beab-47e9edf1ce1e

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_OmittedScoreCell_abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
import Theorems.Thm_Erdos390_Full_OmittedTiltHarmonicRate_tendsto_omittedTiltMajorant_mul_logL_sq_zero
import Theorems.Thm_Erdos390_Full_OmittedTiltHarmonicRate_tendsto_omittedTiltMajorant_mul_logL_zero
import Theorems.Thm_Erdos390_Full_OmittedTiltMarkedProbability_tendsto_omittedTiltMajorant_zero
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_uniformAverage_divInd_paper_bound
import Theorems.Thm_Erdos390_Full_PaperTiltSmallness_eventually_actual_valuationTilt_small

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

theorem coprime_of_mem_primePowerModuli {P : Finset ℕ} {M D a : ℕ}
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (ha : a ∈ primePowerModuli P M) : Nat.Coprime D a := by
  rw [primePowerModuli, Finset.mem_image] at ha
  obtain ⟨pk, hpk, rfl⟩ := ha
  exact (hcop pk.1 (Finset.mem_product.mp hpk).1).pow_right _

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

/-- Fully explicit omitted-local-prime comparison for the true compact
valuation tilt.  The only final hypothesis is the displayed smallness
inequality; in the paper it is enforced by choosing the fixed cutoff `W`
before the compact tilt box.
-/
theorem abs_valuationTilt_divInd_sub_average_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D W : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hW : 1 < W)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpW : ∀ p ∈ P, W ≤ p)
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (heta : ∀ p ∈ P, |eta p| ≤ B)
    (hsmall :
      Real.exp ((B / L) *
          (Real.log (M : ℝ) / Real.log (W : ℝ))) *
          (B / L) *
          ((1 / c) * ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) -
        uniformAverage S (divInd D)| ≤
      (Real.exp ((B / L) *
          (Real.log (M : ℝ) / Real.log (W : ℝ))) *
          (B / L) *
          ((1 / (c * (D : ℝ))) *
            ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) +
        Real.exp ((B / L) *
          (Real.log (M : ℝ) / Real.log (W : ℝ))) *
          uniformAverage S (divInd D) *
          ((B / L) *
            ((1 / c) *
              ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)))) /
        (1 -
          Real.exp ((B / L) *
            (Real.log (M : ℝ) / Real.log (W : ℝ))) *
            (B / L) *
            ((1 / c) *
              ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ))) := by
  let R := primePowerModuli P M
  let beta : ℝ := B / L
  let K : ℝ := beta * (Real.log (M : ℝ) / Real.log (W : ℝ))
  let totalBound : ℝ := (1 / c) * ∑ a ∈ R, 1 / (a : ℝ)
  let markedBound : ℝ :=
    (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ)
  have hbeta : 0 ≤ beta := div_nonneg hB hL.le
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa [R] using ha)
  have hRcop : ∀ a ∈ R, Nat.Coprime D a := by
    intro a ha
    exact coprime_of_mem_primePowerModuli hcop (by simpa [R] using ha)
  have hdom : ∀ m ∈ S,
      |valuationScore P eta L m| ≤ beta * divisorScore R m := by
    intro m hm
    simpa only [beta, R] using
      abs_valuationScore_le_divisorScore P eta hprime (hSpos m hm)
        (hSle m hm) hL heta
  have hscore : ∀ m ∈ S, |valuationScore P eta L m| ≤ K := by
    intro m hm
    simpa only [K, beta] using abs_valuationScore_le_log_ratio P eta
      (hSpos m hm) (hSle m hm) hW hpW hB hL heta
  have htotal : uniformAverage S (divisorScore R) ≤ totalBound := by
    have h := uniformAverage_marked_divisorScore_le S R
      (D := 1) (c := c) (by norm_num) hM hc hcard hSpos hSle hRpos
      (fun a ha ↦ by simp)
    simpa [divInd, totalBound] using h
  have hmarked : uniformAverage S
      (fun m ↦ divInd D m * divisorScore R m) ≤ markedBound := by
    simpa only [markedBound] using
      uniformAverage_marked_divisorScore_le S R hD hM hc hcard
        hSpos hSle hRpos hRcop
  have htotal0 : 0 ≤ totalBound := by
    dsimp only [totalBound]
    positivity
  have hmarked0 : 0 ≤ markedBound := by
    dsimp only [markedBound]
    positivity
  have hsmall' : Real.exp K * beta * totalBound < 1 := by
    simpa only [K, beta, totalBound, R] using hsmall
  simpa only [K, beta, totalBound, markedBound, R] using
    abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
      S R hS D (valuationScore P eta L) hbeta hdom hscore htotal hmarked
      htotal0 hmarked0 hsmall'

end

end Erdos390.Full.ValuationTiltCell

end

/- Source module: Erdos390.Full.PaperTiltSmallness -/
section


/-!
# Non-circular smallness of the actual valuation tilt

The omitted-score denominator is automatically positive at the paper scale.
The fixed box and cutoff enter only through a fixed exponential constant;
the remaining factor is `O(log L / L)`.
-/

open Filter Topology

namespace Erdos390.Full.PaperTiltSmallness

open ArithmeticModel Scale PrimeSums
open DivisibilityMomentBounds FiniteProbability
open ValuationScoreDomination ValuationTiltCell

noncomputable section



/-- The preceding paper-scale estimate dominates the exact prime-power
normalizer for every omitted-score set of primes contained in the actual
band.  In particular, the cutoff set may depend on `n` and may omit one or
two local primes; the threshold is still chosen uniformly before that set. -/
theorem eventually_actual_valuationTilt_small_for_subset
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℕ, P ⊆ primeBand n W →
      Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) *
          ((1 / c) *
            ∑ a ∈ primePowerModuli P (physicalBound C n),
              1 / (a : ℝ)) < 1 := by
  filter_upwards [eventually_actual_valuationTilt_small B C c W hB hC hc hW,
    Filter.eventually_gt_atTop 1] with n hsmall hn
  intro P hP
  have hL : 0 < L n := L_pos hn
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (hP hp)
  have hPsum : (∑ p ∈ P, 1 / (p : ℝ)) ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hP
      (fun p hpBand hpNotP ↦ by positivity)
  have hpowers :
      (∑ a ∈ primePowerModuli P (physicalBound C n), 1 / (a : ℝ)) ≤
        2 * bandReciprocalSum n W := by
    exact (sum_inv_primePowerModuli_le P (physicalBound C n) hprime).trans
      (mul_le_mul_of_nonneg_left hPsum (by norm_num))
  let pref : ℝ :=
    Real.exp
        ((B / L n) *
          (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
      (B / L n) * (1 / c)
  have hpref : 0 ≤ pref := by
    dsimp only [pref]
    positivity
  calc
    Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) *
          ((1 / c) *
            ∑ a ∈ primePowerModuli P (physicalBound C n),
              1 / (a : ℝ)) =
        pref *
          (∑ a ∈ primePowerModuli P (physicalBound C n),
            1 / (a : ℝ)) := by
      dsimp only [pref]
      ring
    _ ≤ pref * (2 * bandReciprocalSum n W) :=
      mul_le_mul_of_nonneg_left hpowers hpref
    _ = Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) * ((2 / c) * bandReciprocalSum n W) := by
      dsimp only [pref]
      ring
    _ < 1 := hsmall

/-- Paper-scale omitted-score comparison with the normalizing-smallness
condition discharged once and for all.  The event in `n` is uniform over the
actual cell, the marked modulus, the box coefficients, and every subset of
the moving prime band.  All remaining hypotheses are literal arithmetic
properties of the chosen cell. -/
theorem eventually_abs_actual_valuationTilt_divInd_sub_average_le
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (S P : Finset ℕ) (eta : ℕ → ℝ) (D : ℕ),
        P ⊆ primeBand n W → ∀ hS : S.Nonempty, 0 < D →
        c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) →
        (∀ m ∈ S, 0 < m) →
        (∀ m ∈ S, m ≤ physicalBound C n) →
        (∀ p ∈ P, Nat.Coprime D p) →
        (∀ p ∈ P, |eta p| ≤ B) →
        |((uniformOnFinset S hS).exponentialTilt
              (fun m : S ↦ valuationScore P eta (L n) m)).expect
              (fun m : S ↦ divInd D m) -
            uniformAverage S (divInd D)| ≤
          (Real.exp ((B / L n) *
              (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
              (B / L n) *
              ((1 / (c * (D : ℝ))) *
                ∑ a ∈ primePowerModuli P (physicalBound C n),
                  1 / (a : ℝ)) +
            Real.exp ((B / L n) *
              (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
              uniformAverage S (divInd D) *
              ((B / L n) *
                ((1 / c) *
                  ∑ a ∈ primePowerModuli P (physicalBound C n),
                    1 / (a : ℝ)))) /
          (1 -
            Real.exp ((B / L n) *
              (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
              (B / L n) *
              ((1 / c) *
                ∑ a ∈ primePowerModuli P (physicalBound C n),
                  1 / (a : ℝ))) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [eventually_actual_valuationTilt_small_for_subset
      B C c W hB hC hc hW, hInvCevent,
    Filter.eventually_gt_atTop 1] with n hsmallAll hInvCn hn
  intro S P eta D hP hS hD hcard hSpos hSle hcop heta
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hphysLower : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  have hM : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one hphysLower
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (hP hp)
  have hpW : ∀ p ∈ P, W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand (hP hp)).le
  exact abs_valuationTilt_divInd_sub_average_le
    S P hS eta hD hM hB hL hW hc hcard hSpos hSle hprime hpW hcop heta
      (hsmallAll P hP)

end

end Erdos390.Full.PaperTiltSmallness

end

/- Source module: Erdos390.Full.OmittedTiltMarkedProbability -/
section


/-!
# Actual omitted-score marked probabilities

This module joins the paper-scale structured-cell count to the genuine
finite valuation tilt.  The local forced primes are omitted from the score,
so their marked modulus is coprime to every score prime.  No marked-number
asymptotic or normalization estimate remains as an input.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.OmittedTiltMarkedProbability

open ArithmeticModel Scale PrimeSums
open StructuredCells HeadPattern
open DivisibilityMomentBounds FiniteProbability
open PaperScaleMarkedCell PaperTiltSmallness ValuationScoreDomination
open DickmanBasic

noncomputable section



theorem eventually_omittedTiltMajorant_nonneg
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ omittedTiltMajorant B C c W n := by
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  unfold omittedTiltMajorant
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (div_nonneg hB hL.le))
    (mul_nonneg (div_nonneg (by norm_num) hc.le) hband)





theorem omittedTiltRemainder_nonneg (K B C c : ℝ) (W n : ℕ) :
    0 ≤ omittedTiltRemainder K B C c W n := by
  unfold omittedTiltRemainder
  have hU : 0 ≤ 1 / rho DickmanBasic.U := one_div_nonneg.mpr rho_U_pos.le
  positivity

theorem tendsto_omittedTiltRemainder_zero
    (K B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    Tendsto (omittedTiltRemainder K B C c W) atTop (𝓝 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hKL : Tendsto (fun n : ℕ ↦ K / L n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLTop
  have hmaj := tendsto_omittedTiltMajorant_zero B C c W hB hC hc hW
  have hbracket : Tendsto
      (fun n : ℕ ↦ 1 + 1 / rho DickmanBasic.U + |K / L n|)
      atTop (𝓝 (1 + 1 / rho DickmanBasic.U)) := by
    simpa using tendsto_const_nhds.add hKL.abs
  have hprod : Tendsto
      (fun n : ℕ ↦ 2 * |omittedTiltMajorant B C c W n| *
        (1 + 1 / rho DickmanBasic.U + |K / L n|))
      atTop (𝓝 0) := by
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    have := (htwo.mul hmaj.abs).mul hbracket
    simpa using this
  change Tendsto
    (fun n : ℕ ↦ |K / L n| +
      2 * |omittedTiltMajorant B C c W n| *
        (1 + 1 / rho DickmanBasic.U + |K / L n|)) atTop (𝓝 0)
  simpa using hKL.abs.add hprod

/-! ## The actual omitted-score marked law -/



end

end Erdos390.Full.OmittedTiltMarkedProbability

end

/- Source module: Erdos390.Full.OmittedTiltHarmonicRate -/
section


/-!
# Harmonic-rate control for the omitted-score remainder

The band-row aggregation in Lemma 7.5 can lose one harmonic factor of order
`log L`.  This file proves directly from the explicit paper remainder that
this loss is harmless: the remainder multiplied by `log L` still tends to
zero.  In particular, the statement does not infer the stronger rate from a
bare `o(1)` estimate.
-/

open Filter Topology

namespace Erdos390.Full.OmittedTiltHarmonicRate

open ArithmeticModel Scale PrimeSums DickmanBasic
open OmittedTiltMarkedProbability
open StructuredCells HeadPattern
open DivisibilityMomentBounds FiniteProbability
open PaperScaleMarkedCell PaperTiltSmallness ValuationScoreDomination

noncomputable section

private theorem tendsto_L_atTop : Tendsto L atTop atTop := by
  simpa [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop





/-- The complete omitted-score remainder absorbs one full harmonic-row
factor.  This is the rate needed when pointwise marked errors are summed over
the moving prime band. -/
theorem tendsto_omittedTiltRemainder_mul_logL_zero
    (K B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    Tendsto
      (fun n : ℕ ↦ omittedTiltRemainder K B C c W n *
        Real.log (L n)) atTop (𝓝 0) := by
  have hLTop : Tendsto L atTop atTop := tendsto_L_atTop
  have hlogRatio : Tendsto
      (fun n : ℕ ↦ Real.log (L n) / L n) atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hKpart : Tendsto
      (fun n : ℕ ↦ |K / L n| * Real.log (L n)) atTop (𝓝 0) := by
    have hbase : Tendsto
        (fun n : ℕ ↦ |K| * (Real.log (L n) / L n)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hlogRatio
    apply hbase.congr'
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hL : 0 < L n := L_pos hn
    rw [abs_div, abs_of_pos hL]
    field_simp [hL.ne']
  have hmajorRate :=
    tendsto_omittedTiltMajorant_mul_logL_zero B C c W hB hC hc hW
  have hlogLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn
    exact Real.log_nonneg hn
  have habsMajorRate : Tendsto
      (fun n : ℕ ↦ |omittedTiltMajorant B C c W n| *
        Real.log (L n)) atTop (𝓝 0) := by
    have heq :
        (fun n : ℕ ↦
          |omittedTiltMajorant B C c W n * Real.log (L n)|) =ᶠ[atTop]
        (fun n : ℕ ↦
          |omittedTiltMajorant B C c W n| * Real.log (L n)) := by
      filter_upwards [hlogLNonneg] with n hlog
      rw [abs_mul, abs_of_nonneg hlog]
    simpa only [abs_zero] using hmajorRate.abs.congr' heq
  have hKL : Tendsto (fun n : ℕ ↦ K / L n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLTop
  have hbracket : Tendsto
      (fun n : ℕ ↦ 1 + 1 / rho DickmanBasic.U + |K / L n|)
      atTop (𝓝 (1 + 1 / rho DickmanBasic.U)) := by
    simpa using tendsto_const_nhds.add hKL.abs
  have hperturbation : Tendsto
      (fun n : ℕ ↦
        (2 * (|omittedTiltMajorant B C c W n| * Real.log (L n))) *
          (1 + 1 / rho DickmanBasic.U + |K / L n|))
      atTop (𝓝 0) := by
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa using (htwo.mul habsMajorRate).mul hbracket
  change Tendsto
    (fun n : ℕ ↦
      (|K / L n| +
        2 * |omittedTiltMajorant B C c W n| *
          (1 + 1 / rho DickmanBasic.U + |K / L n|)) *
        Real.log (L n)) atTop (𝓝 0)
  have heq :
      (fun n : ℕ ↦
        (|K / L n| +
          2 * |omittedTiltMajorant B C c W n| *
            (1 + 1 / rho DickmanBasic.U + |K / L n|)) *
          Real.log (L n)) =
      (fun n : ℕ ↦
        |K / L n| * Real.log (L n) +
          (2 * (|omittedTiltMajorant B C c W n| * Real.log (L n))) *
            (1 + 1 / rho DickmanBasic.U + |K / L n|)) := by
    funext n
    ring
  rw [heq]
  simpa only [add_zero] using hKpart.add hperturbation

/-- The complete omitted-score remainder also survives two harmonic losses. -/
theorem tendsto_omittedTiltRemainder_mul_logL_sq_zero
    (K B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦ omittedTiltRemainder K B C c W n *
      Real.log (L n) ^ 2) atTop (𝓝 0) := by
  have hLTop : Tendsto L atTop atTop := tendsto_L_atTop
  have hlogSqRatio : Tendsto
      (fun n : ℕ ↦ Real.log (L n) ^ 2 / L n) atTop (𝓝 0) := by
    exact Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hKpart : Tendsto (fun n : ℕ ↦
      |K / L n| * Real.log (L n) ^ 2) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ ↦
        |K| * (Real.log (L n) ^ 2 / L n)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hlogSqRatio
    apply hbase.congr'
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hL : 0 < L n := L_pos hn
    rw [abs_div, abs_of_pos hL]
    ring
  have hmajorRate :=
    tendsto_omittedTiltMajorant_mul_logL_sq_zero B C c W hB hC hc hW
  have habsMajorRate : Tendsto (fun n : ℕ ↦
      |omittedTiltMajorant B C c W n| * Real.log (L n) ^ 2)
      atTop (𝓝 0) := by
    have hnonneg := eventually_omittedTiltMajorant_nonneg B C c W hB hc
    apply hmajorRate.congr'
    filter_upwards [hnonneg] with n hn
    rw [abs_of_nonneg hn]
  have hKL : Tendsto (fun n : ℕ ↦ K / L n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLTop
  have hbracket : Tendsto
      (fun n : ℕ ↦ 1 + 1 / rho DickmanBasic.U + |K / L n|)
      atTop (𝓝 (1 + 1 / rho DickmanBasic.U)) := by
    simpa using tendsto_const_nhds.add hKL.abs
  have hperturbation : Tendsto (fun n : ℕ ↦
      (2 * (|omittedTiltMajorant B C c W n| * Real.log (L n) ^ 2)) *
        (1 + 1 / rho DickmanBasic.U + |K / L n|)) atTop (𝓝 0) := by
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa using (htwo.mul habsMajorRate).mul hbracket
  change Tendsto (fun n : ℕ ↦
    (|K / L n| + 2 * |omittedTiltMajorant B C c W n| *
      (1 + 1 / rho DickmanBasic.U + |K / L n|)) *
      Real.log (L n) ^ 2) atTop (𝓝 0)
  have heq : (fun n : ℕ ↦
      (|K / L n| + 2 * |omittedTiltMajorant B C c W n| *
        (1 + 1 / rho DickmanBasic.U + |K / L n|)) *
        Real.log (L n) ^ 2) =
      (fun n : ℕ ↦ |K / L n| * Real.log (L n) ^ 2 +
        (2 * (|omittedTiltMajorant B C c W n| * Real.log (L n) ^ 2)) *
          (1 + 1 / rho DickmanBasic.U + |K / L n|)) := by
    funext n
    ring
  rw [heq]
  simpa only [add_zero] using hKpart.add hperturbation

/-! ## Definitional witness for row aggregation -/

/-- Strengthened form of the actual omitted-score marked law.  Unlike the
older existential interface, this theorem exposes the exact remainder and
its constants, so downstream prime-row summation can invoke the harmonic
rate theorem above without choosing an opaque `epsilon` witness. -/
theorem exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ K c : ℝ, ∃ epsilon : ℕ → ℝ,
      0 ≤ K ∧ 0 < c ∧
      epsilon = omittedTiltRemainder K B C c W ∧
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto epsilon atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2)
        atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n D : ℕ} (P : Finset ℕ) (eta : ℕ → ℝ),
        N₀ ≤ n → 0 < D → D ≤ yNat n ^ 4 →
        D ∈ Nat.smoothNumbers (yNat n + 1) →
        Nat.Coprime D H.modulus →
        P ⊆ primeBand n W →
        (∀ p ∈ P, Nat.Coprime D p) →
        (∀ p ∈ P, |eta p| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦ valuationScore P eta (L n) m)).expect
                (fun m : S ↦ divInd D m) -
              paperDivisibilityMain n D| ≤
            epsilon n / (D : ℝ) := by
  obtain ⟨K, hK, Nbase, hbaseAll⟩ :=
    exists_uniform_uniformAverage_divInd_paper_bound H hA hAC
  obtain ⟨Ndensity, hdensityAll⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let density : ℝ := paperCellDensity H A C
  have hdensity : 0 < density := paperCellDensity_pos H hAC
  let c : ℝ := density / (2 * C)
  have hCpos : 0 < C := hC
  have hc : 0 < c := div_pos hdensity (mul_pos (by norm_num) hCpos)
  let epsilon : ℕ → ℝ := omittedTiltRemainder K B C c W
  have hepsilonDef : epsilon = omittedTiltRemainder K B C c W := rfl
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    exact omittedTiltRemainder_nonneg K B C c W n
  have hepsilonT : Tendsto epsilon atTop (𝓝 0) := by
    exact tendsto_omittedTiltRemainder_zero K B C c W hB hC hc hW
  have hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (𝓝 0) := by
    exact tendsto_omittedTiltRemainder_mul_logL_zero
      K B C c W hB hC hc hW
  have hepsilonRateSq : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2) atTop (𝓝 0) := by
    exact tendsto_omittedTiltRemainder_mul_logL_sq_zero
      K B C c W hB hC hc hW
  have hcompEvent :=
    eventually_abs_actual_valuationTilt_divInd_sub_average_le
      B C c W hB hC hc hW
  have hmajorT := tendsto_omittedTiltMajorant_zero B C c W hB hC hc hW
  have hmajorHalf : ∀ᶠ n : ℕ in atTop,
      omittedTiltMajorant B C c W n ≤ 1 / 2 :=
    hmajorT (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Ncomp, hNcomp⟩ := Filter.eventually_atTop.mp hcompEvent
  have hhalfReady : ∀ᶠ n : ℕ in atTop,
      1 < n ∧ omittedTiltMajorant B C c W n ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_gt_atTop 1, hmajorHalf] with n hn hhalf
    exact ⟨hn, hhalf⟩
  obtain ⟨Nhalf, hNhalf⟩ := Filter.eventually_atTop.mp hhalfReady
  let N₀ := max Nbase (max Ndensity (max Ncomp Nhalf))
  refine ⟨K, c, epsilon, hK.le, hc, hepsilonDef, hepsilon0, hepsilonT,
    hepsilonRate, hepsilonRateSq, N₀, ?_⟩
  intro n D P eta hN hD hD4 hDsmooth hDhead hP hDcop heta
  have hNbase : Nbase ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNdensity : Ndensity ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNcomp' : Ncomp ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNhalf' : Nhalf ≤ n := by
    dsimp only [N₀] at hN
    omega
  obtain ⟨hn, hmajorHalfN⟩ := hNhalf n hNhalf'
  have hcompAll := hNcomp n hNcomp'
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  obtain ⟨hSnonempty, hbase⟩ :=
    hbaseAll hNbase hD hD4 hDsmooth hDhead
  have hcellDensity := hdensityAll hNdensity
  have hMcast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hcard : c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (physicalBound C n : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = density * (n : ℝ) / 2 := by
        dsimp only [c]
        field_simp [hCpos.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S, density] using hcellDensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  refine ⟨by simpa only [S] using hSnonempty, ?_⟩
  intro hS
  have hS' : S.Nonempty := hS
  have hcomp := hcompAll S P eta D hP hS' hD hcard hSpos hSle hDcop heta
  let T : ℝ := ∑ a ∈ primePowerModuli P (physicalBound C n),
    1 / (a : ℝ)
  let g : ℝ := Real.exp ((B / L n) *
    (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)))
  let delta : ℝ := g * (B / L n) * ((1 / c) * T)
  let avg : ℝ := uniformAverage S (divInd D)
  let main : ℝ := paperDivisibilityMain n D
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (hP hp)
  have hTbound : T ≤ 2 * bandReciprocalSum n W := by
    dsimp only [T]
    have hpow := sum_inv_primePowerModuli_le P (physicalBound C n) hprime
    have hPsum : (∑ p ∈ P, 1 / (p : ℝ)) ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      exact Finset.sum_le_sum_of_subset_of_nonneg hP
        (fun p hpBand hpNotP ↦ by positivity)
    exact hpow.trans (mul_le_mul_of_nonneg_left hPsum (by norm_num))
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta, g]
    positivity
  have hdeltaMajor : delta ≤ omittedTiltMajorant B C c W n := by
    have hfactor : 0 ≤ g * (B / L n) * (1 / c) := by
      dsimp only [g]
      positivity
    calc
      delta = (g * (B / L n) * (1 / c)) * T := by
        dsimp only [delta]
        ring
      _ ≤ (g * (B / L n) * (1 / c)) *
          (2 * bandReciprocalSum n W) :=
        mul_le_mul_of_nonneg_left hTbound hfactor
      _ = omittedTiltMajorant B C c W n := by
        unfold omittedTiltMajorant
        dsimp only [g]
        ring
  have hdeltaHalf : delta ≤ 1 / 2 := hdeltaMajor.trans hmajorHalfN
  have hdenpos : 0 < 1 - delta := by linarith
  have hmainBounds := paperDivisibilityMain_nonneg_le hn hD hD4
  have havg0 : 0 ≤ avg := by
    dsimp only [avg, uniformAverage]
    apply div_nonneg
    · exact Finset.sum_nonneg fun m hm ↦ divInd_nonneg D m
    · positivity
  have havgUpper : avg ≤
      1 / (rho DickmanBasic.U * (D : ℝ)) +
        K / ((D : ℝ) * L n) := by
    have hbaseUpper : avg ≤ main + K / ((D : ℝ) * L n) := by
      have habs : avg - main ≤ K / ((D : ℝ) * L n) :=
        (le_abs_self (avg - main)).trans (by
          simpa only [avg, main, S] using hbase)
      linarith
    dsimp only [main] at hbaseUpper
    linarith [hmainBounds.2]
  have hcomp' :
      |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - avg| ≤
        (delta * (1 / (D : ℝ) + avg)) / (1 - delta) := by
    dsimp only [T, g, delta, avg]
    convert hcomp using 1
    ring
  have hsumUpper : 1 / (D : ℝ) + avg ≤
      (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by
    calc
      1 / (D : ℝ) + avg ≤
          1 / (D : ℝ) +
            (1 / (rho DickmanBasic.U * (D : ℝ)) +
              K / ((D : ℝ) * L n)) := by linarith [havgUpper]
      _ = (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by ring
  have hbracket0 : 0 ≤
      (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by
    have : 0 ≤ 1 / rho DickmanBasic.U := one_div_nonneg.mpr rho_U_pos.le
    positivity
  have hnum : delta * (1 / (D : ℝ) + avg) ≤
      omittedTiltMajorant B C c W n *
        ((1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ)) := by
    calc
      delta * (1 / (D : ℝ) + avg) ≤
          delta * ((1 + 1 / rho DickmanBasic.U + K / L n) /
            (D : ℝ)) := mul_le_mul_of_nonneg_left hsumUpper hdelta0
      _ ≤ omittedTiltMajorant B C c W n *
          ((1 + 1 / rho DickmanBasic.U + K / L n) /
            (D : ℝ)) := mul_le_mul_of_nonneg_right hdeltaMajor hbracket0
  have hinvden : 1 / (1 - delta) ≤ 2 := by
    apply (div_le_iff₀ hdenpos).2
    linarith
  have htiltBase :
      |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - avg| ≤
        2 * omittedTiltMajorant B C c W n *
          (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by
    refine hcomp'.trans ?_
    calc
      delta * (1 / (D : ℝ) + avg) / (1 - delta) =
          (delta * (1 / (D : ℝ) + avg)) * (1 / (1 - delta)) := by ring
      _ ≤ (omittedTiltMajorant B C c W n *
          ((1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ))) *
            (1 / (1 - delta)) :=
        mul_le_mul_of_nonneg_right hnum (one_div_nonneg.mpr hdenpos.le)
      _ ≤ (omittedTiltMajorant B C c W n *
          ((1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ))) * 2 :=
        mul_le_mul_of_nonneg_left hinvden
          (mul_nonneg (hdelta0.trans hdeltaMajor) hbracket0)
      _ = 2 * omittedTiltMajorant B C c W n *
          (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) := by ring
  have htriangle :
      |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - main| ≤
        |((uniformOnFinset S hS).exponentialTilt
            (fun m : S ↦ valuationScore P eta (L n) m)).expect
            (fun m : S ↦ divInd D m) - avg| + |avg - main| := by
    exact abs_sub_le _ _ _
  have hmajor0 : 0 ≤ omittedTiltMajorant B C c W n :=
    hdelta0.trans hdeltaMajor
  have hKL0 : 0 ≤ K / L n := div_nonneg hK.le hL.le
  calc
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta (L n) m)).expect
          (fun m : S ↦ divInd D m) - paperDivisibilityMain n D| ≤
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta (L n) m)).expect
          (fun m : S ↦ divInd D m) - avg| + |avg - main| := by
        simpa only [main] using htriangle
    _ ≤ 2 * omittedTiltMajorant B C c W n *
          (1 + 1 / rho DickmanBasic.U + K / L n) / (D : ℝ) +
        K / ((D : ℝ) * L n) := by
      apply add_le_add htiltBase
      simpa only [avg, main, S] using hbase
    _ = epsilon n / (D : ℝ) := by
      dsimp only [epsilon, omittedTiltRemainder]
      rw [abs_of_nonneg hmajor0, abs_of_nonneg hKL0]
      ring

end

end Erdos390.Full.OmittedTiltHarmonicRate

end

theorem solution : Erdos390.RemainingAnalyticGoal001_005 := by
  exact @Erdos390.Full.OmittedTiltHarmonicRate.exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate
