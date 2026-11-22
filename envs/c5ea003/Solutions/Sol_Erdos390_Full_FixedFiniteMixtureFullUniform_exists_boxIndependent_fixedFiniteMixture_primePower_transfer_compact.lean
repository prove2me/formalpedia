-- Prove2me | solution 1 for Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:12:30.999097+00:00
-- url     : https://prove2.me/submissions/d93b8a1c-9420-4b77-8cff-0a0fb1c920fa

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
import Theorems.Thm_Erdos390_Full_FixedFiniteMixtureLemma75_sigmaMixture_primePowerTransferBounds_of_common_profiles_compact
import Theorems.Thm_Erdos390_Full_FullTiltPairHarmonicRate_exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
import Theorems.Thm_Erdos390_Full_LocalFugacityBounds_coefficientTail_le
import Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_mul_logL_sq_zero
import Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_zero_and_rate
import Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerRowRemainder_mul_logL_zero
import Theorems.Thm_Erdos390_Full_PaperPrimePowerTailRow_eventually_tailRowMajorant_le_limit
import Theorems.Thm_Erdos390_Full_PaperPrimePowerTailRow_eventually_tail_row_le
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound



section
theorem Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate : Erdos390.RemainingAnalyticGoal001_004 := @Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles : Erdos390.RemainingAnalyticGoal001_002.{u_1, u_2} := @Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles_compact
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

/-- A global Chebyshev bound for the logarithmically weighted reciprocal
prime sum.  The deliberately simple constant is uniform in the endpoint. -/
theorem fullLogReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullLogReciprocalSum Y ≤ Real.log 4 * (1 + Real.log (Y : ℝ)) := by
  rw [fullLogReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤ Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤
          (Real.log 4 * (Y : ℝ)) / (Y : ℝ) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by field_simp
  have hint :
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
        Real.log 4 * Real.log (Y : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
          ∫ t in (2 : ℝ)..Y, Real.log 4 * (1 / t) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_theta_div_sq hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id ht0))
        · intro t ht
          calc
            Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
            _ = Real.log 4 * (1 / t) := by
              have ht0 : t ≠ 0 := by linarith [ht.1]
              field_simp
      _ = Real.log 4 * Real.log ((Y : ℝ) / 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos (by norm_num) hY0]
      _ ≤ Real.log 4 * Real.log (Y : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlog4
        apply Real.log_le_log (div_pos hY0 (by norm_num))
        linarith
  nlinarith

theorem bandLogReciprocalSum_le_full (n W : ℕ) :
    bandLogReciprocalSum n W ≤ fullLogReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  have hp' : p ≤ yNat n ∧ p.Prime := by
    simpa [primesUpTo] using hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.2.one_le)) (by positivity)

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

private theorem bandTReciprocalSum_eq (n W : ℕ) :
    bandTReciprocalSum n W =
      bandLogReciprocalSum n W / Real.log (y n) := by
  rw [bandTReciprocalSum, bandLogReciprocalSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [tPrime]
  ring

/-- The `t_p/p` mass of the moving prime band is uniformly bounded.  This is
the first-moment estimate used in the weighted covariance-row contraction. -/
theorem eventually_bandTReciprocalSum_le (W : ℕ) :
    ∀ᶠ n in atTop, bandTReciprocalSum n W ≤ 2 * Real.log 4 := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (9 / 2 : ℝ))] with n hn hyn hLn
  have hyNat : 2 ≤ yNat n := by
    exact Nat.le_floor hyn
  have hlogy : 1 ≤ Real.log (y n) := by
    rw [log_y hn]
    nlinarith
  have hlogy0 : 0 < Real.log (y n) := lt_of_lt_of_le (by norm_num) hlogy
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogFloor : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hnum :
      Real.log 4 * (1 + Real.log (yNat n : ℝ)) ≤
        Real.log 4 * (2 * Real.log (y n)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
    nlinarith
  calc
    bandTReciprocalSum n W =
        bandLogReciprocalSum n W / Real.log (y n) := bandTReciprocalSum_eq n W
    _ ≤ fullLogReciprocalSum (yNat n) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right (bandLogReciprocalSum_le_full n W)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (1 + Real.log (yNat n : ℝ))) /
          Real.log (y n) := by
      exact div_le_div_of_nonneg_right (fullLogReciprocalSum_le (yNat n) hyNat)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (2 * Real.log (y n))) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hlogy0)
    _ = 2 * Real.log 4 := by field_simp

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











end

end Erdos390.Full.OmittedTiltPairChamber

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

/- Source module: Erdos390.Full.DickmanFourMarkProductKernel -/
section


/-!
# The four-mark Dickman product kernel

The four-mark chamber in the proof of Lemma 7.5 uses the normalized
Dickman profile

`F x = rho (U - x) / rho U`

on the full simplex `x, z >= 0`, `x + z <= 4`.  The local product estimate
in `DickmanBasic` covers the unit square by differentiating the actual
method-of-steps solution near the origin.  This file extends that estimate
to the whole four-mark simplex using the globally proved one-Lipschitz
bound for `rho` on `[0,5]`.  In particular, no `C^{1,1}` hypothesis and no
tilt-box parameter occurs in the statement or proof.
-/

open Set

noncomputable section

namespace Erdos390.Full.DickmanFourMarkProductKernel

open DickmanBasic FriableAsymptotic















theorem boxIndependentFourMarkKernelConstant_pos :
    0 < boxIndependentFourMarkKernelConstant :=
  (Classical.choose_spec
    exists_boxIndependent_fourMark_productKernel_bound).1

theorem boxIndependentFourMarkKernelConstant_bound
    (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) (hxz : x + z ≤ 4) :
    |fourMarkProfile (x + z) -
        fourMarkProfile x * fourMarkProfile z| ≤
      boxIndependentFourMarkKernelConstant * x * z :=
  (Classical.choose_spec
    exists_boxIndependent_fourMark_productKernel_bound).2 x z hx hz hxz



end Erdos390.Full.DickmanFourMarkProductKernel

end

/- Source module: Erdos390.Full.FullTiltPrimePowerFallback -/
section


/-!
# Arbitrary-power fallback for the genuine full valuation tilt

The sharp Dickman estimate is used only inside the literal four-mark
chamber.  Outside it we need a box-uniform reciprocal bound.  This file
proves that bound directly on the actual structured cell, with the full
prime band present in the score, and derives the corresponding covariance
bound for two distinct primes.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPrimePowerFallback

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open ValuationScoreDomination OmittedTiltFallback
open OmittedTiltPairChamber FullTiltPairChamber
open PaperTwoLocalRestorationBound StructuredCellValuationLaw
open FullTiltPrimePowerCovariance

noncomputable section





/-- **Uniform arbitrary-power fallback for the actual full tilt.**

The ceiling `G₀` depends on the fixed box and cutoff, but not on `n`, the
moving primes, or the exponents.  No four-mark assumption occurs. -/
theorem exists_uniform_fullTilt_primePower_fallback
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ G₀ : ℝ, 0 < G₀ ∧ ∃ N₀ : ℕ,
      ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ G₀ / (D : ℝ) := by
  let c := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  let G₀ := paperPairFallbackCeiling B c W
  have hG₀ : 0 < G₀ := paperPairFallbackCeiling_pos B c W hc
  obtain ⟨Ndensity, hdensity⟩ :=
    PaperScaleMarkedCell.exists_structuredCell_density_lower_bound H hA hAC
  obtain ⟨NG, hG⟩ := Filter.eventually_atTop.mp
    (eventually_paperPairFallbackConstant_le B C c W hB hC hc hW)
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
  let N₀ := max Ndensity (max NG (max Nphys 2))
  refine ⟨G₀, hG₀, N₀, ?_⟩
  intro n eta hN heta
  have hNdensity : Ndensity ≤ n := by dsimp only [N₀] at hN; omega
  have hNG : NG ≤ n := by dsimp only [N₀] at hN; omega
  have hNphys : Nphys ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  change ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
    (valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)).probability.expect
        (fun m ↦ divInd D (m : ℕ)) ≤ G₀ / (D : ℝ)
  intro hS D hD
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
      _ = PaperScaleMarkedCell.paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hCpos.ne']
      _ ≤ (S.card : ℝ) := by simpa only [S] using hcellDensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  have hpW : ∀ z ∈ primeBand n W, W ≤ z := by
    intro z hz
    exact (cutoff_lt_of_mem_primeBand hz).le
  have hraw := omittedValuationTilt_divInd_le S (primeBand n W) hS eta
    hD hMpos hB (L_pos hn) hW hc hcard hSpos hSle hpW heta
  have hGn : paperPairFallbackConstant B C c W n ≤ G₀ := hG n hNG
  have hden0 : 0 ≤ (D : ℝ) := by positivity
  calc
    (valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd D (m : ℕ)) ≤
      paperPairFallbackConstant B C c W n / (D : ℝ) := by
        simpa only [StructuredCellValuationLaw.valuationTilt_probability,
          paperPairFallbackConstant, S, div_div] using hraw
    _ ≤ G₀ / (D : ℝ) :=
      div_le_div_of_nonneg_right hGn hden0



end

end Erdos390.Full.FullTiltPrimePowerFallback

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section









theorem pairWeight_eq_single_mul (p q r s : ℕ) :
    pairWeight p q r s = singleWeight p r * singleWeight q s := by
  unfold pairWeight singleWeight
  ring

theorem pairWeight_nonneg (p q r s : ℕ) :
    0 ≤ pairWeight p q r s := by
  unfold pairWeight
  positivity









theorem localRestorationScale_nonneg {G k : ℝ}
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ localRestorationScale G k := by
  unfold localRestorationScale
  positivity

theorem pairProbabilityScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ pairProbabilityScale epsilon G k := by
  unfold pairProbabilityScale
  have hlocal := localRestorationScale_nonneg hG hk
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem aggregateChamberScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ aggregateChamberScale epsilon G k := by
  unfold aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  exact add_nonneg (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)) hE

/-- Two pointwise coefficient-tail bounds imply a product-weighted bound
for the complete two-local restoration error. -/
theorem pairRestorationError_le_pairWeight
    {p q Ap Aq r s : ℕ} {etaP etaQ L₀ G G₀ k : ℝ}
    (hG : G ≤ G₀) (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hpTail : coefficientTail p Ap r etaP L₀ ≤
      k * (((r : ℝ) + 1) / (p : ℝ) ^ r))
    (hqTail : coefficientTail q Aq s etaQ L₀ ≤
      k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :
    pairRestorationError p q Ap Aq r s etaP etaQ L₀ G ≤
      localRestorationScale G₀ k * pairWeight p q r s := by
  let dp := coefficientTail p Ap r etaP L₀
  let dq := coefficientTail q Aq s etaQ L₀
  have hdp0 : 0 ≤ dp := coefficientTail_nonneg _ _ _ _ _
  have hdq0 : 0 ≤ dq := coefficientTail_nonneg _ _ _ _ _
  have hpden0 : 0 ≤ (p : ℝ) ^ r := by positivity
  have hqden0 : 0 ≤ (q : ℝ) ^ s := by positivity
  have hpInv0 : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hqInv0 : 0 ≤ 1 / (q : ℝ) ^ s := by positivity
  have hdp : dp ≤ k * (((r : ℝ) + 1) / (p : ℝ) ^ r) := hpTail
  have hdq : dq ≤ k * (((s : ℝ) + 1) / (q : ℝ) ^ s) := hqTail
  have hGdp : G * dp ≤
      G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r)) :=
    mul_le_mul hG hdp hdp0 hG₀
  have hGdq : G * dq ≤
      G₀ * (k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :=
    mul_le_mul hG hdq hdq0 hG₀
  have htermP : G * dp * (1 / (q : ℝ) ^ s) ≤
      G₀ * k * pairWeight p q r s := by
    calc
      G * dp * (1 / (q : ℝ) ^ s) ≤
          (G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r))) *
            (1 / (q : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_right hGdp hqInv0
      _ = (G₀ * k * ((r : ℝ) + 1) *
          (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s)) := by ring
      _ ≤ (G₀ * k * ((r : ℝ) + 1) *
          (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s)) *
            ((s : ℝ) + 1) := by
        have hbase : 0 ≤ G₀ * k * ((r : ℝ) + 1) *
            (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s) := by positivity
        nlinarith
      _ = G₀ * k * pairWeight p q r s := by
        unfold pairWeight
        ring
  have htermQ : G * (1 / (p : ℝ) ^ r) * dq ≤
      G₀ * k * pairWeight p q r s := by
    calc
      G * (1 / (p : ℝ) ^ r) * dq = (G * dq) *
          (1 / (p : ℝ) ^ r) := by ring
      _ ≤ (G₀ * (k * (((s : ℝ) + 1) / (q : ℝ) ^ s))) *
          (1 / (p : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_right hGdq hpInv0
      _ = (G₀ * k * ((s : ℝ) + 1) *
          (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r)) := by ring
      _ ≤ (G₀ * k * ((s : ℝ) + 1) *
          (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r)) *
            ((r : ℝ) + 1) := by
        have hbase : 0 ≤ G₀ * k * ((s : ℝ) + 1) *
            (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r) := by positivity
        nlinarith
      _ = G₀ * k * pairWeight p q r s := by
        unfold pairWeight
        ring
  have htermPQ : G * dp * dq ≤
      G₀ * k ^ 2 * pairWeight p q r s := by
    calc
      G * dp * dq ≤
          (G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r))) *
            (k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :=
        mul_le_mul hGdp hdq hdq0 (by positivity)
      _ = G₀ * k ^ 2 * pairWeight p q r s := by
        unfold pairWeight
        ring
  unfold pairRestorationError localRestorationScale
  dsimp only [dp, dq] at htermP htermQ htermPQ
  calc
    _ ≤ G₀ * k * pairWeight p q r s +
        G₀ * k * pairWeight p q r s +
          G₀ * k ^ 2 * pairWeight p q r s :=
      add_le_add_three htermP htermQ htermPQ
    _ = G₀ * (2 * k + k ^ 2) * pairWeight p q r s := by ring

/-- A small algebraic adapter used for the main-times-restoration term.
Keeping this estimate separate makes all sign assumptions explicit. -/
theorem abs_mul_le_scaled_weight
    {a b R E dInv w : ℝ}
    (ha : |a| ≤ R * dInv) (hb₀ : 0 ≤ b) (hb : b ≤ E)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hdInv : 0 ≤ dInv)
    (hdInvw : dInv ≤ w) :
    |a| * b ≤ (R * E) * w := by
  have hprod : |a| * b ≤ (R * dInv) * E :=
    mul_le_mul ha hb hb₀ (mul_nonneg hR hdInv)
  have hscale : 0 ≤ R * E := mul_nonneg hR hE
  calc
    |a| * b ≤ (R * dInv) * E := hprod
    _ = (R * E) * dInv := by ring
    _ ≤ (R * E) * w := mul_le_mul_of_nonneg_left hdInvw hscale





/-- The explicit full-pair probability error is bounded by one scalar times
the natural product weight. -/
theorem fullPairChamberError_le_pairWeight
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) {G₀ k : ℝ}
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hepsilon : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (ValuationCutoff.valuationCutoff z (physicalBound C n))
        u (eta z) (L n) ≤
          k * (((u : ℝ) + 1) / (z : ℝ) ^ u)) :
    fullPairChamberError H A C B W n p q r s eta epsilon ≤
      pairProbabilityScale (epsilon n) G₀ k * pairWeight p q r s := by
  let G := paperPairFallbackConstant B C (pairFallbackDensity H A C) W n
  let Ap := ValuationCutoff.valuationCutoff p (physicalBound C n)
  let Aq := ValuationCutoff.valuationCutoff q (physicalBound C n)
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hG0 : 0 ≤ G := paperPairFallbackConstant_nonneg _ _ _ _ _ hc
  have hrs := pairRestorationError_le_pairWeight hG hG₀ hk
    (hcoef p hpBand r) (hcoef q hqBand s)
  have h00raw := pairRestorationError_le_pairWeight hG hG₀ hk
    (hcoef p hpBand 0) (hcoef q hqBand 0)
  have hweight00 : pairWeight p q 0 0 = 1 := by
    simp [pairWeight]
  have h00 : pairRestorationError p q Ap Aq 0 0
      (eta p) (eta q) (L n) G ≤ localRestorationScale G₀ k := by
    simpa only [Ap, Aq, G, hweight00, mul_one] using h00raw
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hmainRaw := paperDivisibilityMain_nonneg_le hn hDpos hD4
  have hmain : |paperDivisibilityMain n (pairPower p q r s)| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
    rw [abs_of_nonneg hmainRaw.1]
    convert hmainRaw.2 using 1
    all_goals
      simp only [pairPower, Nat.cast_mul, Nat.cast_pow]
      ring
  have hweightOne :
      1 / ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤ pairWeight p q r s := by
    unfold pairWeight
    have hden0 : 0 ≤ (p : ℝ) ^ r * (q : ℝ) ^ s := by positivity
    have hnum : (1 : ℝ) ≤ ((r : ℝ) + 1) * ((s : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ r by positivity,
        show (0 : ℝ) ≤ s by positivity]
    exact div_le_div_of_nonneg_right hnum hden0
  have heps : epsilon n / (pairPower p q r s : ℝ) ≤
      epsilon n * pairWeight p q r s := by
    norm_num only [pairPower, Nat.cast_mul, Nat.cast_pow]
    have hmul := mul_le_mul_of_nonneg_left hweightOne hepsilon
    simpa [div_eq_mul_inv] using hmul
  calc
    fullPairChamberError H A C B W n p q r s eta epsilon =
        2 * (pairRestorationError p q Ap Aq r s
            (eta p) (eta q) (L n) G +
          epsilon n / (pairPower p q r s : ℝ) +
          |paperDivisibilityMain n (pairPower p q r s)| *
            pairRestorationError p q Ap Aq 0 0
              (eta p) (eta q) (L n) G) := by
      rfl
    _ ≤ 2 * (localRestorationScale G₀ k * pairWeight p q r s +
        epsilon n * pairWeight p q r s +
        ((1 / DickmanBasic.rho DickmanBasic.U) *
          localRestorationScale G₀ k) * pairWeight p q r s) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_three hrs heps
          (abs_mul_le_scaled_weight
            (by simpa [div_eq_mul_inv] using hmain)
            (pairRestorationError_nonneg _ _ _ _ _ _ _ _ _ _ hG0) h00
            (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
            (localRestorationScale_nonneg hG₀ hk) (by positivity)
            hweightOne))
        (by norm_num)
    _ = pairProbabilityScale (epsilon n) G₀ k *
        pairWeight p q r s := by
      unfold pairProbabilityScale
      ring



end

end Erdos390.Full.PaperPrimePowerChamberError

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

lemma card_jiBeyondFour_le (n p q A : ℕ) :
    (jiBeyondFour n p q A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

lemma card_ijBeyondFour_le (n p q A : ℕ) :
    (ijBeyondFour n p q A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

lemma card_jjBeyondFour_le (n p q A B : ℕ) :
    (jjBeyondFour n p q A B).card ≤ A * B := by
  calc
    (jjBeyondFour n p q A B).card ≤
        ((highExponents A).product (highExponents B)).card :=
      Finset.card_filter_le _ _
    _ = (highExponents A).card * (highExponents B).card :=
      Finset.card_product _ _
    _ ≤ A * B := Nat.mul_le_mul (card_highExponents_le A)
      (card_highExponents_le B)

lemma card_diagonalBeyondFour_le (n p A : ℕ) :
    (diagonalBeyondFour n p A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

/-- A `JI` modulus beyond `yNat^4` has at least one full extra factor
`yNat` after its first two `p` marks. -/
lemma yNat_lt_pow_sub_two_of_jiBeyondFour
    {n p q A r : ℕ} (hr : r ∈ jiBeyondFour n p q A)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n < p ^ (r - 2) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hfour : yNat n ^ 4 < p ^ r * q := (Finset.mem_filter.mp hr).2
  by_contra hnot
  have hexcess : p ^ (r - 2) ≤ yNat n := Nat.le_of_not_gt hnot
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hfactor : p ^ r = p ^ (r - 2) * p ^ 2 := by
    calc
      p ^ r = p ^ ((r - 2) + 2) := by
        congr 1
        omega
      _ = p ^ (r - 2) * p ^ 2 := pow_add _ _ _
  have hupper : p ^ r * q ≤ yNat n ^ 4 := by
    calc
      p ^ r * q = (p ^ (r - 2) * p ^ 2) * q := by rw [hfactor]
      _ ≤ (yNat n * yNat n ^ 2) * yNat n :=
        Nat.mul_le_mul (Nat.mul_le_mul hexcess hp2) hqY
      _ = yNat n ^ 4 := by ring
  omega

/-- Transposed one-high-power excess. -/
lemma yNat_lt_pow_sub_two_of_ijBeyondFour
    {n p q A s : ℕ} (hs : s ∈ ijBeyondFour n p q A)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n < q ^ (s - 2) := by
  have hs2 : 2 ≤ s := (mem_highExponents.mp (Finset.mem_filter.mp hs).1).1
  have hfour : yNat n ^ 4 < p * q ^ s := (Finset.mem_filter.mp hs).2
  by_contra hnot
  have hexcess : q ^ (s - 2) ≤ yNat n := Nat.le_of_not_gt hnot
  have hq2 : q ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hqY 2
  have hfactor : q ^ s = q ^ 2 * q ^ (s - 2) := by
    calc
      q ^ s = q ^ (2 + (s - 2)) := by
        congr 1
        omega
      _ = q ^ 2 * q ^ (s - 2) := pow_add _ _ _
  have hupper : p * q ^ s ≤ yNat n ^ 4 := by
    calc
      p * q ^ s = p * (q ^ 2 * q ^ (s - 2)) := by rw [hfactor]
      _ ≤ yNat n * (yNat n ^ 2 * yNat n) :=
        Nat.mul_le_mul hpY (Nat.mul_le_mul hq2 hexcess)
      _ = yNat n ^ 4 := by ring
  omega

/-- Pointwise reciprocal bound for a literal `JI` tail exponent. -/
lemma jiBeyondFour_reciprocal_le
    {n p q A r : ℕ} (hr : r ∈ jiBeyondFour n p q A)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) ^ r * (q : ℝ)) ≤
      1 / ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hexcess := yNat_lt_pow_sub_two_of_jiBeyondFour hr hpY hqY
  have hfactor : (p : ℝ) ^ r * (q : ℝ) =
      ((p : ℝ) ^ 2 * (q : ℝ)) * (p : ℝ) ^ (r - 2) := by
    calc
      (p : ℝ) ^ r * (q : ℝ) =
          (p : ℝ) ^ (2 + (r - 2)) * (q : ℝ) := by
            congr 2
            omega
      _ = ((p : ℝ) ^ 2 * (q : ℝ)) * (p : ℝ) ^ (r - 2) := by
        rw [pow_add]
        ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  gcongr
  exact_mod_cast hexcess.le

/-- Pointwise reciprocal bound in the transposed orientation. -/
lemma ijBeyondFour_reciprocal_le
    {n p q A s : ℕ} (hs : s ∈ ijBeyondFour n p q A)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) * (q : ℝ) ^ s) ≤
      1 / ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  have hs2 : 2 ≤ s := (mem_highExponents.mp (Finset.mem_filter.mp hs).1).1
  have hexcess := yNat_lt_pow_sub_two_of_ijBeyondFour hs hpY hqY
  have hfactor : (p : ℝ) * (q : ℝ) ^ s =
      ((p : ℝ) * (q : ℝ) ^ 2) * (q : ℝ) ^ (s - 2) := by
    calc
      (p : ℝ) * (q : ℝ) ^ s =
          (p : ℝ) * (q : ℝ) ^ (2 + (s - 2)) := by
            congr 2
            omega
      _ = ((p : ℝ) * (q : ℝ) ^ 2) * (q : ℝ) ^ (s - 2) := by
        rw [pow_add]
        ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  gcongr
  exact_mod_cast hexcess.le

/-- The complete finite `JI` reciprocal tail: the only multiplicity loss is
the actual exponent cutoff. -/
theorem sum_jiBeyondFour_reciprocal_le
    {n p q A : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ r ∈ jiBeyondFour n p q A,
        1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
      (A : ℝ) /
        ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))
  calc
    (∑ r ∈ jiBeyondFour n p q A,
        1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
        ∑ _r ∈ jiBeyondFour n p q A, K := by
      apply Finset.sum_le_sum
      intro r hr
      exact jiBeyondFour_reciprocal_le hr hp0 hq0 hY0 hpY hqY
    _ = ((jiBeyondFour n p q A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_jiBeyondFour_le n p q A) (by positivity)
    _ = (A : ℝ) /
        ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- The complete finite `IJ` reciprocal tail. -/
theorem sum_ijBeyondFour_reciprocal_le
    {n p q A : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ s ∈ ijBeyondFour n p q A,
        1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
      (A : ℝ) /
        ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))
  calc
    (∑ s ∈ ijBeyondFour n p q A,
        1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
        ∑ _s ∈ ijBeyondFour n p q A, K := by
      apply Finset.sum_le_sum
      intro s hs
      exact ijBeyondFour_reciprocal_le hs hp0 hq0 hY0 hpY hqY
    _ = ((ijBeyondFour n p q A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_ijBeyondFour_le n p q A) (by positivity)
    _ = (A : ℝ) /
        ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- Taking a positive cube root converts the integer inequality
`Y^2 < D^3` into the exact `Y^(2/3) < D` scale used in the paper's `JJ`
tail. -/
lemma rpow_two_thirds_lt_of_sq_lt_cube {Y D : ℕ}
    (hY0 : 0 < Y) (hD0 : 0 < D) (h : Y ^ 2 < D ^ 3) :
    (Y : ℝ) ^ (2 / 3 : ℝ) < (D : ℝ) := by
  have hcast : (Y : ℝ) ^ 2 < (D : ℝ) ^ 3 := by exact_mod_cast h
  have hr := Real.rpow_lt_rpow (show 0 ≤ (Y : ℝ) ^ 2 by positivity)
    hcast (show 0 < (1 / 3 : ℝ) by norm_num)
  have hleft : ((Y : ℝ) ^ 2) ^ (1 / 3 : ℝ) =
      (Y : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show 0 ≤ (Y : ℝ) by positivity)]
    congr 1
    norm_num
  have hright : ((D : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (D : ℝ) := by
    simpa [one_div] using Real.pow_rpow_inv_natCast
      (show 0 ≤ (D : ℝ) by positivity) (show (3 : ℕ) ≠ 0 by norm_num)
  rw [hleft, hright] at hr
  exact hr

private lemma pow_le_excess_cube {p r : ℕ} (hp0 : 0 < p) (hr3 : 3 ≤ r) :
    p ^ r ≤ (p ^ (r - 2)) ^ 3 := by
  calc
    p ^ r ≤ p ^ ((r - 2) * 3) :=
      Nat.pow_le_pow_right hp0 (by omega)
    _ = (p ^ (r - 2)) ^ 3 := pow_mul _ _ _

/-- Every literal `JJ` tail pair has excess prime-power product larger
than `yNat^(2/3)`.  The proof treats the one-high and two-high exponent
orientations separately, exactly as in the paper. -/
lemma yNat_sq_lt_excess_cube_of_jjBeyondFour
    {n p q A B r s : ℕ} (hrs : (r, s) ∈ jjBeyondFour n p q A B)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n ^ 2 < (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by
  have hrs' := Finset.mem_filter.mp hrs
  have hrmem : r ∈ highExponents A := (Finset.mem_product.mp hrs'.1).1
  have hsmem : s ∈ highExponents B := (Finset.mem_product.mp hrs'.1).2
  have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
  have hs2 : 2 ≤ s := (mem_highExponents.mp hsmem).1
  have hfour : yNat n ^ 4 < p ^ r * q ^ s := hrs'.2
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hq2 : q ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hqY 2
  by_cases hrEq : r = 2
  · subst r
    have hsNe : s ≠ 2 := by
      intro hsEq
      subst s
      have hupper : p ^ 2 * q ^ 2 ≤ yNat n ^ 4 := by
        calc
          p ^ 2 * q ^ 2 ≤ yNat n ^ 2 * yNat n ^ 2 :=
            Nat.mul_le_mul hp2 hq2
          _ = yNat n ^ 4 := by ring
      omega
    have hs3 : 3 ≤ s := by omega
    have hqPow : yNat n ^ 2 < q ^ s := by
      by_contra hnot
      have hqPowLe : q ^ s ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
      have hupper : p ^ 2 * q ^ s ≤ yNat n ^ 4 := by
        calc
          p ^ 2 * q ^ s ≤ yNat n ^ 2 * yNat n ^ 2 :=
            Nat.mul_le_mul hp2 hqPowLe
          _ = yNat n ^ 4 := by ring
      omega
    have hqCube := pow_le_excess_cube hq0 hs3
    simpa using hqPow.trans_le hqCube
  · have hr3 : 3 ≤ r := by omega
    by_cases hsEq : s = 2
    · subst s
      have hpPow : yNat n ^ 2 < p ^ r := by
        by_contra hnot
        have hpPowLe : p ^ r ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
        have hupper : p ^ r * q ^ 2 ≤ yNat n ^ 4 := by
          calc
            p ^ r * q ^ 2 ≤ yNat n ^ 2 * yNat n ^ 2 :=
              Nat.mul_le_mul hpPowLe hq2
            _ = yNat n ^ 4 := by ring
        omega
      have hpCube := pow_le_excess_cube hp0 hr3
      simpa using hpPow.trans_le hpCube
    · have hs3 : 3 ≤ s := by omega
      have hpCube := pow_le_excess_cube hp0 hr3
      have hqCube := pow_le_excess_cube hq0 hs3
      have htotalCube : p ^ r * q ^ s ≤
          (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by
        calc
          p ^ r * q ^ s ≤
              (p ^ (r - 2)) ^ 3 * (q ^ (s - 2)) ^ 3 :=
            Nat.mul_le_mul hpCube hqCube
          _ = (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by ring
      have hY24 : yNat n ^ 2 ≤ yNat n ^ 4 :=
        Nat.pow_le_pow_right hY0 (by norm_num)
      exact hY24.trans_lt (hfour.trans_le htotalCube)

/-- Pointwise `JJ` reciprocal tail with the exact two-thirds power. -/
lemma jjBeyondFour_reciprocal_le
    {n p q A B r s : ℕ} (hrs : (r, s) ∈ jjBeyondFour n p q A B)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤
      1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
        (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  have hrs' := Finset.mem_filter.mp hrs
  have hrmem : r ∈ highExponents A := (Finset.mem_product.mp hrs'.1).1
  have hsmem : s ∈ highExponents B := (Finset.mem_product.mp hrs'.1).2
  have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
  have hs2 : 2 ≤ s := (mem_highExponents.mp hsmem).1
  have hexcessCube := yNat_sq_lt_excess_cube_of_jjBeyondFour
    hrs hp0 hq0 hY0 hpY hqY
  have hexcessPos : 0 < p ^ (r - 2) * q ^ (s - 2) := by positivity
  have hexcess := rpow_two_thirds_lt_of_sq_lt_cube hY0 hexcessPos hexcessCube
  have hfactor : (p : ℝ) ^ r * (q : ℝ) ^ s =
      ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) *
        ((p : ℝ) ^ (r - 2) * (q : ℝ) ^ (s - 2)) := by
    calc
      (p : ℝ) ^ r * (q : ℝ) ^ s =
          ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) *
            ((q : ℝ) ^ 2 * (q : ℝ) ^ (s - 2)) := by
              congr 2
              · rw [← pow_add]
                congr 1
                omega
              · rw [← pow_add]
                congr 1
                omega
      _ = ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) *
          ((p : ℝ) ^ (r - 2) * (q : ℝ) ^ (s - 2)) := by ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hexcess.le

/-- The complete finite `JJ` reciprocal tail, with precisely the product of
the two actual exponent cutoffs as multiplicity. -/
theorem sum_jjBeyondFour_reciprocal_le
    {n p q A B : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ rs ∈ jjBeyondFour n p q A B,
        1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
      ((A : ℝ) * (B : ℝ)) /
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
    (yNat n : ℝ) ^ (2 / 3 : ℝ))
  calc
    (∑ rs ∈ jjBeyondFour n p q A B,
        1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
        ∑ _rs ∈ jjBeyondFour n p q A B, K := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact jjBeyondFour_reciprocal_le hrs hp0 hq0 hY0 hpY hqY
    _ = ((jjBeyondFour n p q A B).card : ℝ) * K := by simp
    _ ≤ ((A : ℝ) * (B : ℝ)) * K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_jjBeyondFour_le n p q A B
    _ = ((A : ℝ) * (B : ℝ)) /
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
      simp [K, div_eq_mul_inv]

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





lemma cutoffScale_pos {W : ℕ} (hW : 1 < W) : 0 < cutoffScale W := by
  unfold cutoffScale
  exact div_pos (by norm_num) (Real.log_pos (by exact_mod_cast hW))

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

/-- Paper-scale `JI` reciprocal tail with the actual valuation cutoff.  Its
coefficient depends on `W` but not on the tilt box. -/
theorem eventually_actual_ji_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ jiBeyondFour n p q (actualExponentCutoff C n p),
          1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
        (cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  exact (sum_jiBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right (hcut p hp) (by positivity))

/-- Paper-scale transposed reciprocal tail. -/
theorem eventually_actual_ij_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ ijBeyondFour n p q (actualExponentCutoff C n q),
          1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
        (cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  exact (sum_ijBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right (hcut q hq) (by positivity))

/-- Paper-scale `JJ` reciprocal tail with the exact `yNat^(-2/3)` decay. -/
theorem eventually_actual_jj_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ rs ∈ jjBeyondFour n p q
          (actualExponentCutoff C n p) (actualExponentCutoff C n q),
          1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
        ((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hnum :
      (actualExponentCutoff C n p : ℝ) *
          (actualExponentCutoff C n q : ℝ) ≤
        (cutoffScale W * L n) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hcut p hp) (hcut q hq) (by positivity) hscale0
  exact (sum_jjBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right hnum (by positivity))

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



lemma sixtyFour_le_pairAggregationConstant :
    (64 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  linarith [quadraticHalfMass_nonneg]



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)











end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerFourDisplays -/
section


/-!
# The four pointwise displays of Lemma 7.5

This file is the exact algebraic specialization of the generic actual-law
splice to `JI`, `IJ`, `JJ`, and the diagonal second-moment input.  One main
constant and one chamber remainder dominate all four orientations.
-/

namespace Erdos390.Full.PaperPrimePowerFourDisplays

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PaperPrimePowerChamberError PaperPrimePowerPointwise

noncomputable section















theorem primePowerChamberRemainder_nonneg
    {epsilon G₀ k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k) :
    0 ≤ primePowerChamberRemainder epsilon G₀ k :=
  aggregateChamberScale_nonneg hepsilon hG₀ hk









end

end Erdos390.Full.PaperPrimePowerFourDisplays

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

theorem sum_eJI_eq
    (G : ℝ) (n p q A : ℕ) :
    (∑ r ∈ highExponents A, eJI G n p q r) =
      (G + G ^ 2) *
        (∑ r ∈ jiBeyondFour n p q A,
          1 / ((p : ℝ) ^ r * (q : ℝ))) := by
  unfold eJI covarianceTail jiBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [pairPower, pow_one]
  by_cases hle : p ^ r * q ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p ^ r * q := Nat.not_lt_of_ge hle
    simp only [if_pos hle, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p ^ r * q := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

theorem sum_eIJ_eq
    (G : ℝ) (n p q A : ℕ) :
    (∑ s ∈ highExponents A, eIJ G n p q s) =
      (G + G ^ 2) *
        (∑ s ∈ ijBeyondFour n p q A,
          1 / ((p : ℝ) * (q : ℝ) ^ s)) := by
  unfold eIJ covarianceTail ijBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [pairPower, pow_one]
  by_cases hle : p * q ^ s ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p * q ^ s := Nat.not_lt_of_ge hle
    simp only [if_pos hle, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p * q ^ s := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

theorem sum_eJJ_eq
    (G : ℝ) (n p q A B : ℕ) :
    (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        eJJ G n p q r s) =
      (G + G ^ 2) *
        (∑ rs ∈ jjBeyondFour n p q A B,
          1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) := by
  unfold eJJ covarianceTail jjBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  calc
    (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        if pairPower p q r s ≤ yNat n ^ 4 then 0
        else (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)) =
      (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        if yNat n ^ 4 < p ^ r * q ^ s then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ r * (q : ℝ) ^ s)) else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      simp only [pairPower]
      by_cases hle : p ^ r * q ^ s ≤ yNat n ^ 4
      · have hnlt : ¬ yNat n ^ 4 < p ^ r * q ^ s := Nat.not_lt_of_ge hle
        simp only [if_pos hle, if_neg hnlt]
      · have hlt : yNat n ^ 4 < p ^ r * q ^ s := Nat.lt_of_not_ge hle
        simp only [if_neg hle, if_pos hlt]
        ring
    _ = ∑ rs ∈ (highExponents A).product (highExponents B),
        if yNat n ^ 4 < p ^ rs.1 * q ^ rs.2 then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) else 0 := by
      symm
      exact Finset.sum_product (highExponents A) (highExponents B)
        (fun rs ↦ if yNat n ^ 4 < p ^ rs.1 * q ^ rs.2 then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) else 0)

theorem sum_weighted_eD_eq
    (G : ℝ) (n p A : ℕ) :
    (∑ r ∈ highExponents A,
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) =
      G * (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
  unfold eD probabilityTail diagonalBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hle : p ^ r ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p ^ r := Nat.not_lt_of_ge hle
    simp only [if_pos hle, mul_zero, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p ^ r := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

/-- Actual-cutoff bound for the `JI` residual sum. -/
theorem eventually_sum_eJI_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p), eJI G n p q r) ≤
        (G + G ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))) := by
  filter_upwards [eventually_actual_ji_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eJI_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the `IJ` residual sum. -/
theorem eventually_sum_eIJ_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (actualExponentCutoff C n q), eIJ G n p q s) ≤
        (G + G ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))) := by
  filter_upwards [eventually_actual_ij_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eIJ_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the `JJ` residual sum. -/
theorem eventually_sum_eJJ_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        ∑ s ∈ highExponents (actualExponentCutoff C n q), eJJ G n p q r s) ≤
        (G + G ^ 2) * (((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ))) := by
  filter_upwards [eventually_actual_jj_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eJJ_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the weighted diagonal residual sum. -/
theorem eventually_sum_weighted_eD_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
        G * ((2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
  filter_upwards [eventually_actual_diagonal_weighted_reciprocal_tail_le
    C W hC hW] with n htail
  intro p hp
  rw [sum_weighted_eD_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp) hG

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

/-- A polynomial in `log n` is negligible compared with every fixed
positive power of `n`. -/
private theorem tendsto_L_sq_div_nat_rpow_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n ^ 2 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) ^ a)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat



theorem tendsto_tailRowLimitMajorant_zero (G : ℝ) (W : ℕ) :
    Tendsto (tailRowLimitMajorant G W) atTop (nhds 0) := by
  have h1 := tendsto_L_sq_div_nat_rpow_zero
    (show (0 : ℝ) < 1 / 5 by norm_num)
  have h2 := tendsto_L_sq_div_nat_rpow_zero
    (show (0 : ℝ) < 2 / 15 by norm_num)
  have h3 := tendsto_L_sq_div_nat_rpow_zero
    (show (0 : ℝ) < 2 / 5 by norm_num)
  have hc1 : Tendsto
      (fun _n : ℕ ↦ 13 * (G + G ^ 2) * cutoffScale W)
      atTop (nhds (13 * (G + G ^ 2) * cutoffScale W)) :=
    tendsto_const_nhds
  have ht1 : Tendsto (fun n : ℕ ↦
      (13 * (G + G ^ 2) * cutoffScale W) *
        (L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hc1.mul h1
  have hc2 : Tendsto
      (fun _n : ℕ ↦ (G + G ^ 2) * cutoffScale W ^ 2)
      atTop (nhds ((G + G ^ 2) * cutoffScale W ^ 2)) :=
    tendsto_const_nhds
  have ht2 : Tendsto (fun n : ℕ ↦
      ((G + G ^ 2) * cutoffScale W ^ 2) *
        (L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hc2.mul h2
  have hc3 : Tendsto
      (fun _n : ℕ ↦ 6 * G * cutoffScale W ^ 2)
      atTop (nhds (6 * G * cutoffScale W ^ 2)) :=
    tendsto_const_nhds
  have ht3 : Tendsto (fun n : ℕ ↦
      (6 * G * cutoffScale W ^ 2) *
        (L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hc3.mul h3
  unfold tailRowLimitMajorant
  dsimp only
  simpa only [add_zero] using (ht1.add ht2).add ht3



/-- The complete literal beyond-four residual row vanishes. -/
theorem tendsto_tailRowMajorant_zero
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Tendsto (tailRowMajorant G W) atTop (nhds 0) := by
  have hupper := eventually_tailRowMajorant_le_limit G W hG hW
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ tailRowMajorant G W n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    exact tailRowMajorant_nonneg hG hW hn
  exact squeeze_zero' hlower hupper (tendsto_tailRowLimitMajorant_zero G W)

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

/- Source module: Erdos390.Full.PaperPrimePowerRemainderRate -/
section


/-!
# Common vanishing remainder for Lemma 7.5

The omitted-score error must survive one complete harmonic prime sum.  This
file propagates the strengthened `epsilon * log L -> 0` estimate through the
local restoration and covariance polynomials, and then combines it with the
literal beyond-four row.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerRemainderRate

open ArithmeticModel Scale PrimeSums
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation PaperPrimePowerTailRow

noncomputable section

private theorem tendsto_const_mul_zero
    (a : ℝ) {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ a * f n) atTop (nhds 0) := by
  have ha : Tendsto (fun _n : ℕ ↦ a) atTop (nhds a) :=
    tendsto_const_nhds
  simpa only [mul_zero] using ha.mul hf













theorem tendsto_primePowerRowRemainder_zero
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (nhds 0))
    (hepsilon0 : ∀ n, 0 ≤ epsilon n) (hG₀ : 0 ≤ G₀)
    (hB : 0 ≤ B) (hGf : 0 ≤ Gf) (hW : 1 < W) :
    Tendsto (primePowerRowRemainder epsilon G₀ B Gf W) atTop (nhds 0) := by
  obtain ⟨hchamber, hchamberRate⟩ :=
    tendsto_primePowerChamberRemainder_zero_and_rate
      epsilon G₀ B W hepsilon hepsilonRate
  let R : ℕ → ℝ := fun n ↦
    primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n)
  let upper : ℕ → ℝ := fun n ↦
    pairAggregationConstant *
      (12 * (R n * Real.log (L n)) + 5 * R n) * (1 / (W : ℝ))
  have hupperT : Tendsto upper atTop (nhds 0) := by
    have hscaledRate := tendsto_const_mul_zero 12 hchamberRate
    have hscaled := tendsto_const_mul_zero 5 hchamber
    have hsum := hscaledRate.add hscaled
    have hsum0 : Tendsto (fun n : ℕ ↦
        12 * (primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) * Real.log (L n)) +
        5 * primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n)) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have houterLeft := tendsto_const_mul_zero pairAggregationConstant hsum0
    have houter := tendsto_const_mul_zero (1 / (W : ℝ)) houterLeft
    apply houter.congr'
    filter_upwards with n
    unfold upper
    dsimp only [R]
    ring
  have hchamberNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ R n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    unfold R
    exact primePowerChamberRemainder_nonneg
      (hepsilon0 n) hG₀ (by
        unfold coefficientScale
        have hL := L_pos hn
        positivity)
  have hbandUpper : ∀ᶠ n : ℕ in atTop,
      pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ)) ≤ upper n := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      hchamberNonneg] with n hband hR
    unfold upper
    have hAgg : 0 ≤ pairAggregationConstant := pairAggregationConstant_nonneg
    have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
    have hinside : R n * (bandReciprocalSum n W + 5) ≤
        12 * (R n * Real.log (L n)) + 5 * R n := by
      nlinarith [mul_le_mul_of_nonneg_left hband hR]
    calc
      pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ)) =
        (pairAggregationConstant * (R n * (bandReciprocalSum n W + 5))) *
          (1 / (W : ℝ)) := by ring
      _ ≤ (pairAggregationConstant *
          (12 * (R n * Real.log (L n)) + 5 * R n)) *
            (1 / (W : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinside hAgg) hWinv
      _ = upper n := by rfl
  have hbandNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
        (1 / (W : ℝ)) := by
    filter_upwards [hchamberNonneg] with n hR
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg pairAggregationConstant_nonneg hR)
        (by linarith))
      (by positivity)
  have hbandT := squeeze_zero' hbandNonneg hbandUpper hupperT
  have htail := tendsto_tailRowMajorant_zero Gf W hGf hW
  unfold primePowerRowRemainder
  simpa only [R, add_zero] using hbandT.add htail



end

end Erdos390.Full.PaperPrimePowerRemainderRate

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



/-- Two fixed primes above `W`; the selected one is always different from
the current row prime. -/
theorem exists_eventually_auxiliaryPrime
    (W : ℕ) :
    ∃ q₀ q₁ : ℕ, ∃ aux : ℕ → ℕ,
      q₀.Prime ∧ q₁.Prime ∧ W < q₀ ∧ q₀ < q₁ ∧
      aux = (fun p ↦ if p = q₀ then q₁ else q₀) ∧
      ∀ᶠ n : ℕ in atTop,
        q₀ ∈ primeBand n W ∧ q₁ ∈ primeBand n W ∧
          ∀ p ∈ primeBand n W,
            aux p ∈ (primeBand n W).erase p := by
  obtain ⟨q₀, hWq₀, hq₀⟩ := Nat.exists_infinite_primes (W + 1)
  obtain ⟨q₁, hq₀q₁, hq₁⟩ := Nat.exists_infinite_primes (q₀ + 1)
  let aux : ℕ → ℕ := fun p ↦ if p = q₀ then q₁ else q₀
  have hWltq₀ : W < q₀ := by omega
  have hq₀ltq₁ : q₀ < q₁ := by omega
  have hyTop : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hreach : ∀ᶠ n : ℕ in atTop, (q₁ : ℝ) ≤ y n :=
    hyTop.eventually (eventually_ge_atTop (q₁ : ℝ))
  refine ⟨q₀, q₁, aux, hq₀, hq₁, hWltq₀, hq₀ltq₁, rfl, ?_⟩
  filter_upwards [hreach] with n hqn
  have hq₁Y : q₁ ≤ yNat n := Nat.le_floor hqn
  have hq₀Y : q₀ ≤ yNat n := hq₀ltq₁.le.trans hq₁Y
  have hq₀Band : q₀ ∈ primeBand n W :=
    mem_primeBand.mpr ⟨hq₀, hWltq₀, hq₀Y⟩
  have hq₁Band : q₁ ∈ primeBand n W :=
    mem_primeBand.mpr ⟨hq₁, hWltq₀.trans hq₀ltq₁, hq₁Y⟩
  refine ⟨hq₀Band, hq₁Band, ?_⟩
  intro p hpBand
  by_cases hpq₀ : p = q₀
  · have hq₁p : q₁ ≠ p := by omega
    simpa only [aux, if_pos hpq₀] using
      (Finset.mem_erase.mpr ⟨hq₁p, hq₁Band⟩)
  · have hq₀p : q₀ ≠ p := by exact fun h ↦ hpq₀ h.symm
    simpa only [aux, if_neg hpq₀] using
      (Finset.mem_erase.mpr ⟨hq₀p, hq₀Band⟩)

end

end Erdos390.Full.PaperPrimePowerAuxiliaryPrime

end

/- Source module: Erdos390.Full.PaperPrimePowerLemma75 -/
section


/-!
# Exact export of paper Lemma 7.5

This module joins the literal four-mark chamber, the arbitrary-power
fallback, the four prime-power orientations, and their finite row
aggregation.  The final constant is independent of the tilt box.  All box
dependence is confined to a single remainder tending to zero.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerLemma75

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open DickmanFourMarkProductKernel
open FullTiltPairChamber FullTiltPairHarmonicRate
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber PaperScaleMarkedCell LocalFugacityBounds
open PaperTwoLocalRestorationBound PaperValuationCutoff
open PaperPrimePowerChamberError PaperPrimePowerActualSplice
open PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerSumAbsAggregation
open ValuationCutoff PrimeSums PaperPrimePowerRow

noncomputable section





theorem paperPrimePowerConstant_pos {C_K : ℝ} (hCK : 0 < C_K) :
    0 < paperPrimePowerConstant C_K := by
  unfold paperPrimePowerConstant
  have hAgg : 0 < pairAggregationConstant :=
    lt_of_lt_of_le (by norm_num) sixtyFour_le_pairAggregationConstant
  have hMain : 0 < primePowerMainConstant C_K := by
    unfold primePowerMainConstant
    exact add_pos (mul_pos (by norm_num) hCK)
      (one_div_pos.mpr DickmanBasic.rho_U_pos)
  exact mul_pos (mul_pos hAgg hMain) (by positivity)





theorem PrimePowerTransferBounds.mono_epsilon
    {Omega : Type*} [Fintype Omega] {M n W : ℕ}
    {law : BoundedValuationLaw Omega M} {C_pow epsilon₁ epsilon₂ : ℝ}
    (hε : epsilon₁ ≤ epsilon₂)
    (h : PrimePowerTransferBounds law n W C_pow epsilon₁) :
    PrimePowerTransferBounds law n W C_pow epsilon₂ := by
  refine {
    ji := ?_
    ij := ?_
    jj := ?_
    diagonal := ?_
    row := ?_ }
  · intro p hp q hq
    exact (h.ji p hp q hq).trans (by gcongr)
  · intro p hp q hq
    exact (h.ij p hp q hq).trans (by gcongr)
  · intro p hp q hq
    exact (h.jj p hp q hq).trans (by gcongr)
  · intro p hp
    exact (h.diagonal p hp).trans (by gcongr)
  · intro p hp
    exact (h.row p hp).trans (add_le_add le_rfl hε)





end

end Erdos390.Full.PaperPrimePowerLemma75

end

/- Source module: Erdos390.Full.FixedFiniteMixtureFullUniform -/
section


/-!
# Full uniform Lemma 7.5 for a fixed finite family of actual cells

This file specializes the marked-cell and full-tilt asymptotics on every
member of a fixed finite family, takes finite common majorants, and applies
the exact tagged-mixture theorem.  No desired covariance or tail estimate
is assumed by the final export.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureFullUniform

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate FullTiltPrimePowerFallback
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixtureLemma75 PaperValuationCutoff ValuationCutoff
open PrimeSums

noncomputable section





theorem pairProbabilityScale_le_primePowerChamberRemainder
    {epsilon G k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    pairProbabilityScale epsilon G k ≤
      primePowerChamberRemainder epsilon G k := by
  unfold primePowerChamberRemainder aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  have hcov := pairCovarianceScale_nonneg hE
  linarith



variable {Cell : Type*} [Fintype Cell]



theorem boxIndependentPrimePowerConstant_pos :
    0 < boxIndependentPrimePowerConstant :=
  paperPrimePowerConstant_pos boxIndependentFourMarkKernelConstant_pos

/-- **Full fixed-finite-mixture export of paper Lemma 7.5.**

`H`, `A`, and `C` describe the fixed component cells.  `Cmax` is any fixed
common physical upper endpoint.  The constant is chosen before the tilt
box.  The one common remainder is nonnegative and tends to zero, and all
mixture weights are allowed (including the partition-function-reweighted
weights produced by a global exponential tilt). -/
theorem exists_boxIndependent_fixedFiniteMixture_primePower_transfer
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    0 < boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
        (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
      ∀ B : ℝ, 0 ≤ B →
      ∃ epsilon_BW : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon_BW n) ∧
        Tendsto epsilon_BW atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            ∀ weight : FiniteProbability Cell,
              let law := fun c ↦ widen
                (valuationTilt (H c) (physicalBound (A c) n)
                  (physicalBound (C c) n) (yNat n) (hS c)
                  (primeBand n W) eta (L n))
                (physicalBound_mono (hC_le c) n)
              PrimePowerTransferBounds (sigmaMixture weight law) n W
                boxIndependentPrimePowerConstant (epsilon_BW n) := by
  let C_K : ℝ := boxIndependentFourMarkKernelConstant
  let C_pow : ℝ := boxIndependentPrimePowerConstant
  have hCK : 0 < C_K := by
    simpa only [C_K] using boxIndependentFourMarkKernelConstant_pos
  have hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |DickmanBasic.F (x + z) - DickmanBasic.F x * DickmanBasic.F z| ≤
        C_K * x * z := by
    intro x z hx hz hxz
    simpa only [C_K, fourMarkProfile_eq_F] using
      boxIndependentFourMarkKernelConstant_bound x z hx hz hxz
  refine ⟨boxIndependentPrimePowerConstant_pos, ?_⟩
  intro W hW hHW B hB
  have hpairExists : ∀ c, ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto epsilon atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2)
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p →
        pairPower p q r s ≤ yNat n ^ 4 →
        Nat.Coprime p (H c).modulus → Nat.Coprime q (H c).modulus →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := structuredCell (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
              (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
              (fun m : S ↦ divInd (pairPower p q r s) m) -
            paperDivisibilityMain n (pairPower p q r s)| ≤
          fullPairChamberError (H c) (A c) (C c) B W n p q r s
            eta epsilon := by
    intro c
    exact exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose epsilon hepsilonData using hpairExists
  have hepsilon0 (c : Cell) : ∀ n, 0 ≤ epsilon c n :=
    (hepsilonData c).1
  have hepsilonT (c : Cell) : Tendsto (epsilon c) atTop (nhds 0) :=
    (hepsilonData c).2.1
  have hepsilonRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ epsilon c n * Real.log (L n)) atTop (nhds 0) :=
    (hepsilonData c).2.2.1
  have hepsilonRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ epsilon c n * Real.log (L n) ^ 2) atTop (nhds 0) :=
    (hepsilonData c).2.2.2.1
  choose Npair hpairRaw using fun c ↦ (hepsilonData c).2.2.2.2
  have hfallbackExists : ∀ c, ∃ Gf : ℝ, 0 < Gf ∧ ∃ N₀ : ℕ,
      ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n) hS
          (primeBand n W) eta (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ Gf / (D : ℝ) := by
    intro c
    exact exists_uniform_fullTilt_primePower_fallback
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose Gcell hGcellData using hfallbackExists
  have hGcell (c : Cell) : 0 < Gcell c := (hGcellData c).1
  choose Nfallback hfallbackRaw using fun c ↦ (hGcellData c).2
  let cden : Cell → ℝ := fun c ↦ pairFallbackDensity (H c) (A c) (C c)
  let G₀ : Cell → ℝ := fun c ↦ paperPairFallbackCeiling B (cden c) W
  let cellRemainder : Cell → ℕ → ℝ := fun c n ↦
    primePowerChamberRemainder (epsilon c n) (G₀ c)
      (coefficientScale B W n)
  let profile : ℕ → ℝ := fun n ↦ ∑ c, |cellRemainder c n|
  let halfProfile : ℕ → ℝ := fun n ↦ profile n / 2
  let Gf : ℝ := ∑ c, Gcell c
  have hGf : 0 ≤ Gf := by
    dsimp only [Gf]
    exact Finset.sum_nonneg fun c hc ↦ (hGcell c).le
  have hcellRemainderT (c : Cell) :
      Tendsto (cellRemainder c) atTop (nhds 0) := by
    simpa only [cellRemainder] using
      (tendsto_primePowerChamberRemainder_zero_and_rate
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRate c)).1
  have hcellRemainderRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ cellRemainder c n * Real.log (L n))
        atTop (nhds 0) := by
    simpa only [cellRemainder] using
      (tendsto_primePowerChamberRemainder_zero_and_rate
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRate c)).2
  have hcellRemainderRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ cellRemainder c n * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    simpa only [cellRemainder] using
      tendsto_primePowerChamberRemainder_mul_logL_sq_zero
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRateSq c)
  have hprofileT : Tendsto profile atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ (hcellRemainderT c).abs)
    simpa only [profile, abs_zero, Finset.sum_const_zero] using hsum
  have hlogLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) := by
    have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
      hLTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hLge] with n hn
    exact Real.log_nonneg hn
  have hcellAbsRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ |cellRemainder c n| * Real.log (L n))
        atTop (nhds 0) := by
    have habs := (hcellRemainderRate c).abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |cellRemainder c n * Real.log (L n)|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards [hlogLNonneg] with n hlog
    rw [abs_mul, abs_of_nonneg hlog]
  have hprofileRate : Tendsto
      (fun n : ℕ ↦ profile n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hcellAbsRate c)
    have hsum0 : Tendsto
        (fun n : ℕ ↦ ∑ c, |cellRemainder c n| * Real.log (L n))
          atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [profile]
    rw [Finset.sum_mul]
  have hcellAbsRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ |cellRemainder c n| * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    have habs := (hcellRemainderRateSq c).abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |cellRemainder c n * Real.log (L n) ^ 2|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards with n
    have hsq : |Real.log (L n) ^ 2| = Real.log (L n) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    rw [abs_mul, hsq]
  have hprofileRateSq : Tendsto
      (fun n : ℕ ↦ profile n * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hcellAbsRateSq c)
    have hsum0 : Tendsto
        (fun n : ℕ ↦ ∑ c, |cellRemainder c n| * Real.log (L n) ^ 2)
          atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [profile]
    rw [Finset.sum_mul]
  have hhalf0 : ∀ n, 0 ≤ halfProfile n := by
    intro n
    dsimp only [halfProfile, profile]
    positivity
  have hhalfT : Tendsto halfProfile atTop (nhds 0) := by
    have htwo : Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa only [halfProfile, zero_div] using hprofileT.div_const 2
  have hhalfRate : Tendsto
      (fun n : ℕ ↦ halfProfile n * Real.log (L n)) atTop (nhds 0) := by
    have h := hprofileRate.div_const 2
    have h0 : Tendsto
        (fun n : ℕ ↦ profile n * Real.log (L n) / 2)
          atTop (nhds 0) := by simpa only [zero_div] using h
    apply h0.congr'
    filter_upwards with n
    dsimp only [halfProfile]
    ring
  have hhalfRateSq : Tendsto
      (fun n : ℕ ↦ halfProfile n * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    have h := hprofileRateSq.div_const 2
    have h0 : Tendsto
        (fun n : ℕ ↦ profile n * Real.log (L n) ^ 2 / 2)
          atTop (nhds 0) := by simpa only [zero_div] using h
    apply h0.congr'
    filter_upwards with n
    dsimp only [halfProfile]
    ring
  let Eagg : ℕ → ℝ := fun n ↦
    primePowerChamberRemainder (halfProfile n) 0 0
  have hEaggT : Tendsto Eagg atTop (nhds 0) := by
    have hraw := (tendsto_primePowerChamberRemainder_zero_and_rate
      halfProfile 0 0 W hhalfT hhalfRate).1
    simpa only [Eagg, coefficientScale_zero] using hraw
  have hEaggRate : Tendsto
      (fun n : ℕ ↦ Eagg n * Real.log (L n)) atTop (nhds 0) := by
    have hraw := (tendsto_primePowerChamberRemainder_zero_and_rate
      halfProfile 0 0 W hhalfT hhalfRate).2
    simpa only [Eagg, coefficientScale_zero] using hraw
  let tail : ℕ → ℝ := tailRowMajorant Gf W
  have htailT : Tendsto tail atTop (nhds 0) := by
    simpa only [tail] using tendsto_tailRowMajorant_zero Gf W hGf hW
  have htailRate : Tendsto
      (fun n : ℕ ↦ tail n * Real.log (L n)) atTop (nhds 0) := by
    simpa only [tail] using
      tendsto_tailRowMajorant_mul_logL_zero Gf W hGf hW
  have hrowRemainderT := tendsto_primePowerRowRemainder_zero
    halfProfile 0 0 Gf W hhalfT hhalfRate hhalf0 (by norm_num)
      (by norm_num) hGf hW
  have hrowRemainderRate := tendsto_primePowerRowRemainder_mul_logL_zero
    halfProfile 0 0 Gf W hhalfT hhalfRate hhalfRateSq hhalf0
      (by norm_num) (by norm_num) hGf hW
  let rawRemainder : ℕ → ℝ := fun n ↦
    genericAggregationRemainder (Eagg n) (tail n) (tail n) (tail n)
      (tail n) n W
  have hrawRemainderT : Tendsto rawRemainder atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦ pairAggregationConstant * Eagg n)
        atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ pairAggregationConstant) atTop
          (nhds pairAggregationConstant) := tendsto_const_nhds
      simpa only [mul_zero] using hc.mul hEaggT
    have hthree : Tendsto (fun n : ℕ ↦ 3 * tail n) atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
        tendsto_const_nhds
      simpa only [mul_zero] using hc.mul htailT
    have hsum := (hscaled.add hthree).add hrowRemainderT
    have hsum0 : Tendsto
        (fun n : ℕ ↦ pairAggregationConstant * Eagg n + 3 * tail n +
          primePowerRowRemainder halfProfile 0 0 Gf W n)
          atTop (nhds 0) := by simpa only [add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold rawRemainder genericAggregationRemainder
    unfold primePowerRowRemainder
    dsimp only [tail, Eagg]
    rw [coefficientScale_zero]
    ring
  have hrawRemainderRate : Tendsto
      (fun n : ℕ ↦ rawRemainder n * Real.log (L n))
        atTop (nhds 0) := by
    have hscaled : Tendsto
        (fun n : ℕ ↦
          pairAggregationConstant * (Eagg n * Real.log (L n)))
        atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ pairAggregationConstant) atTop
          (nhds pairAggregationConstant) := tendsto_const_nhds
      simpa only [mul_zero] using hc.mul hEaggRate
    have hthree : Tendsto
        (fun n : ℕ ↦ 3 * (tail n * Real.log (L n)))
        atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
        tendsto_const_nhds
      simpa only [mul_zero] using hc.mul htailRate
    have hsum := (hscaled.add hthree).add hrowRemainderRate
    have hsum0 : Tendsto
        (fun n : ℕ ↦
          pairAggregationConstant * (Eagg n * Real.log (L n)) +
            3 * (tail n * Real.log (L n)) +
              primePowerRowRemainder halfProfile 0 0 Gf W n *
                Real.log (L n)) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold rawRemainder genericAggregationRemainder
    unfold primePowerRowRemainder
    dsimp only [tail, Eagg]
    rw [coefficientScale_zero]
    ring
  let epsilon_BW : ℕ → ℝ := fun n ↦ |rawRemainder n|
  have hepsilon_BW0 : ∀ n, 0 ≤ epsilon_BW n := fun n ↦ abs_nonneg _
  have hepsilon_BWT : Tendsto epsilon_BW atTop (nhds 0) := by
    simpa only [epsilon_BW, abs_zero] using hrawRemainderT.abs
  have hepsilon_BWRate : Tendsto
      (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
        atTop (nhds 0) := by
    have habs := hrawRemainderRate.abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |rawRemainder n * Real.log (L n)|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards [hlogLNonneg] with n hlog
    dsimp only [epsilon_BW]
    rw [abs_mul, abs_of_nonneg hlog]
  obtain ⟨q₀, q₁, aux, _, _, _, hq₀q₁, _, hauxEvent⟩ :=
    exists_eventually_auxiliaryPrime W
  have hcden (c : Cell) : 0 < cden c := by
    dsimp only [cden]
    exact pairFallbackDensity_pos_of_pos (H c) (hAC c) (hC c)
  have hG₀ (c : Cell) : 0 < G₀ c := by
    dsimp only [G₀]
    exact paperPairFallbackCeiling_pos B (cden c) W (hcden c)
  have hNpairEvent : ∀ᶠ n : ℕ in atTop, ∀ c, Npair c ≤ n := by
    rw [Filter.eventually_all]
    intro c
    exact eventually_ge_atTop (Npair c)
  have hNfallbackEvent : ∀ᶠ n : ℕ in atTop,
      ∀ c, Nfallback c ≤ n := by
    rw [Filter.eventually_all]
    intro c
    exact eventually_ge_atTop (Nfallback c)
  have hGEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      paperPairFallbackConstant B (C c) (cden c) W n ≤ G₀ c := by
    rw [Filter.eventually_all]
    intro c
    simpa only [G₀] using eventually_paperPairFallbackConstant_le
      B (C c) (cden c) W hB (hC c) (hcden c) hW
  have hcoefEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      ∀ p ∈ primeBand n W, ∀ eta₀ : ℝ, |eta₀| ≤ B → ∀ r : ℕ,
      coefficientTail p (valuationCutoff p (physicalBound (C c) n))
          r eta₀ (L n) ≤ coefficientScale B W n *
            (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
    rw [Filter.eventually_all]
    intro c
    simpa only [coefficientScale] using
      eventually_coefficientTail_le_of_pos B (C c) W hB (hC c) hW
  have htailJIEvent := eventually_sum_eJI_le Gf Cmax W hGf hCmax hW
  have htailIJEvent := eventually_sum_eIJ_le Gf Cmax W hGf hCmax hW
  have htailJJEvent := eventually_sum_eJJ_le Gf Cmax W hGf hCmax hW
  have htailDEvent := eventually_sum_weighted_eD_le
    Gf Cmax W hGf hCmax hW
  have htailRowEvent := eventually_tail_row_le Gf Cmax W hGf hCmax hW
  have hbandTEvent := eventually_bandTReciprocalSum_le W
  have hfinal : ∀ᶠ n : ℕ in atTop, ∀ eta : ℕ → ℝ,
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := fun c ↦ structuredCell (H c)
        (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
      (∀ c, (S c).Nonempty) ∧
        ∀ hS : ∀ c, (S c).Nonempty,
        ∀ weight : FiniteProbability Cell,
          let law := fun c ↦ widen
            (valuationTilt (H c) (physicalBound (A c) n)
              (physicalBound (C c) n) (yNat n) (hS c)
              (primeBand n W) eta (L n))
            (physicalBound_mono (hC_le c) n)
          PrimePowerTransferBounds (sigmaMixture weight law) n W
            C_pow (epsilon_BW n) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hNpairEvent,
      hNfallbackEvent, hGEvent, hcoefEvent, htailJIEvent,
      htailIJEvent, htailJJEvent, htailDEvent, htailRowEvent,
      hbandTEvent, hauxEvent]
      with n hn hNpairn hNfallbackn hGn hcoefn htailJIn htailIJn
        htailJJn htailDn htailRown hbandTn hauxn
    intro eta heta
    obtain ⟨hq₀Band, hq₁Band, hauxn⟩ := hauxn
    have hq₁Erase : q₁ ∈ (primeBand n W).erase q₀ :=
      Finset.mem_erase.mpr ⟨hq₀q₁.ne', hq₁Band⟩
    let S := fun c ↦ structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
    have hSnonempty : ∀ c, (S c).Nonempty := by
      intro c
      have hq₀Head := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hq₀Band
      have hq₁Head := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hq₁Band
      have hyPos : 0 < yNat n :=
        (prime_of_mem_primeBand hq₀Band).pos.trans_le
          (le_yNat_of_mem_primeBand hq₀Band)
      have hzero : pairPower q₀ q₁ 0 0 ≤ yNat n ^ 4 := by
        simpa only [pairPower, pow_zero, mul_one] using
          (one_le_pow₀ (show 1 ≤ yNat n from hyPos))
      have hseed := hpairRaw c eta (hNpairn c) hq₀Band hq₁Erase
        hzero hq₀Head hq₁Head heta
      simpa only [S] using hseed.1
    refine ⟨hSnonempty, ?_⟩
    intro hS weight
    let baseLaw := fun c ↦
      valuationTilt (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n) (hS c)
        (primeBand n W) eta (L n)
    let law := fun c ↦ widen (baseLaw c)
      (physicalBound_mono (hC_le c) n)
    have hk : 0 ≤ coefficientScale B W n := by
      unfold coefficientScale
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hB) (L_pos hn).le)
        (Real.exp_pos _).le
    have hprofileCell : ∀ c p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
        pairPower p q r s ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (pairPower p q r s)
              ((law c).value omega)) -
          paperDivisibilityMain n (pairPower p q r s)| ≤
          profile n * pairWeight p q r s := by
      intro c p hpBand q hqErase r s hD4
      have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
      have hpHead := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hpBand
      have hqHead := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hqBand
      have hraw := (hpairRaw c eta (hNpairn c) hpBand hqErase hD4
        hpHead hqHead heta).2 (hS c)
      have herr := fullPairChamberError_le_pairWeight
        (H c) eta (epsilon c) hn hpBand hqBand hD4
        (hepsilon0 c n)
        (show 0 ≤ pairFallbackDensity (H c) (A c) (C c) by
          exact (hcden c).le)
        (by simpa only [cden, G₀] using hGn c) (hG₀ c).le hk
        (fun z hz u ↦ hcoefn c z hz (eta z) (heta z hz) u)
      have hprobToCell :
          pairProbabilityScale (epsilon c n) (G₀ c)
              (coefficientScale B W n) ≤ cellRemainder c n := by
        exact pairProbabilityScale_le_primePowerChamberRemainder
          (hepsilon0 c n) (hG₀ c).le hk
      have hcellToProfile : cellRemainder c n ≤ profile n := by
        calc
          cellRemainder c n ≤ |cellRemainder c n| := le_abs_self _
          _ ≤ ∑ d, |cellRemainder d n| := by
            exact Finset.single_le_sum
              (fun d hd ↦ abs_nonneg (cellRemainder d n))
              (Finset.mem_univ c)
          _ = profile n := rfl
      have hscale := mul_le_mul_of_nonneg_right
        (hprobToCell.trans hcellToProfile) (pairWeight_nonneg p q r s)
      have hbound := hraw.trans (herr.trans hscale)
      simpa only [law, baseLaw, widen_probability, widen_value,
        valuationTilt_probability, valuationTilt_value] using hbound
    have hpairProfile : ∀ c p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
        pairPower p q r s ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (pairPower p q r s)
              ((law c).value omega)) -
          paperDivisibilityMain n (pairPower p q r s)| ≤
          pairProbabilityScale (halfProfile n) 0 0 *
            pairWeight p q r s := by
      simpa only [halfProfile, pairProbabilityScale_half_zero] using
        hprofileCell
    have hsingleProfile : ∀ c p, p ∈ primeBand n W → ∀ r,
        p ^ r ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (p ^ r) ((law c).value omega)) -
          paperDivisibilityMain n (p ^ r)| ≤
          pairProbabilityScale (halfProfile n) 0 0 * singleWeight p r := by
      intro c p hpBand r hD4
      let q := aux p
      have hqErase : q ∈ (primeBand n W).erase p := hauxn p hpBand
      have hpair := hpairProfile c p hpBand q hqErase r 0
        (by simpa only [pairPower, pow_zero, mul_one] using hD4)
      simpa only [pairPower, pow_zero, mul_one, pairWeight_eq_single_mul,
        singleWeight, Nat.cast_zero, zero_add, div_one, mul_one] using hpair
    have hfallback : ∀ c D, 0 < D →
        (law c).probability.expect
          (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ) := by
      intro c D hD
      have hraw := hfallbackRaw c eta (hNfallbackn c) heta (hS c) D hD
      have hcellLe : Gcell c ≤ Gf := by
        dsimp only [Gf]
        exact Finset.single_le_sum
          (fun d hd ↦ (hGcell d).le) (Finset.mem_univ c)
      have hdiv := div_le_div_of_nonneg_right hcellLe (by positivity :
        0 ≤ (D : ℝ))
      have hbound := hraw.trans hdiv
      simpa only [law, baseLaw, widen_probability, widen_value,
        valuationTilt_probability, valuationTilt_value] using hbound
    let T : ℝ := Gf + Gf ^ 2
    let K : ℝ := cutoffScale W * L n
    let Y : ℝ := yNat n
    have hT : 0 ≤ T := by
      dsimp only [T]
      nlinarith [sq_nonneg Gf]
    have hK : 0 ≤ K := by
      dsimp only [K]
      exact mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
    have hY : 0 < Y := by
      dsimp only [Y]
      exact_mod_cast (prime_of_mem_primeBand hq₀Band).pos.trans_le
        (le_yNat_of_mem_primeBand hq₀Band)
    have hband0 : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    have hTailLinear : T * (K / Y) ≤ tail n := by
      dsimp only [tail]
      unfold tailRowMajorant
      dsimp only [T, K, Y]
      have hKY : 0 ≤ K / Y := div_nonneg hK hY.le
      have hfirst : T * (K / Y) ≤
          T * ((K / Y) * (bandReciprocalSum n W + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith [mul_nonneg hKY hband0]
      have hsecond : 0 ≤ T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by
        positivity
      have hthird : 0 ≤ 6 * Gf * (K ^ 2 / Y ^ 2) := by positivity
      linarith
    have hTailQuadratic : T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) ≤ tail n := by
      dsimp only [tail]
      unfold tailRowMajorant
      dsimp only [T, K, Y]
      have hfirst : 0 ≤
          T * ((K / Y) * (bandReciprocalSum n W + 1)) := by positivity
      have hthird : 0 ≤ 6 * Gf * (K ^ 2 / Y ^ 2) := by positivity
      linarith
    have hTailDiagonal : 2 * Gf * (K ^ 2 / Y ^ 2) ≤ tail n := by
      dsimp only [tail]
      unfold tailRowMajorant
      dsimp only [T, K, Y]
      have hfirst : 0 ≤
          T * ((K / Y) * (bandReciprocalSum n W + 1)) := by positivity
      have hsecond : 0 ≤ T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by positivity
      have hthird : 2 * Gf * (K ^ 2 / Y ^ 2) ≤
          6 * Gf * (K ^ 2 / Y ^ 2) := by
        have hx : 0 ≤ Gf * (K ^ 2 / Y ^ 2) := by positivity
        nlinarith
      linarith
    have htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound Cmax n)),
          eJI Gf n p q r) ≤
          tail n * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by
      intro p hp q hq
      calc
        _ ≤ (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
            ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))) := by
          simpa only [actualExponentCutoff] using htailJIn p hp q hq
        _ = (T * (K / Y)) * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) := by dsimp only [T, K, Y]; ring
        _ ≤ _ := by gcongr
    have htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
        (∑ s ∈ highExponents (valuationCutoff q (physicalBound Cmax n)),
          eIJ Gf n p q s) ≤
          tail n * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by
      intro p hp q hq
      calc
        _ ≤ (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
            ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))) := by
          simpa only [actualExponentCutoff] using htailIJn p hp q hq
        _ = (T * (K / Y)) * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 := by dsimp only [T, K, Y]; ring
        _ ≤ _ := by gcongr
    have htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound Cmax n)),
          ∑ s ∈ highExponents (valuationCutoff q (physicalBound Cmax n)),
            eJJ Gf n p q r s) ≤
          tail n * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
      intro p hp q hq
      calc
        _ ≤ (Gf + Gf ^ 2) * (((cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
              (yNat n : ℝ) ^ (2 / 3 : ℝ))) := by
          simpa only [actualExponentCutoff] using htailJJn p hp q hq
        _ = (T * (K ^ 2 / Y ^ (2 / 3 : ℝ))) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
          dsimp only [T, K, Y]; ring
        _ ≤ _ := by gcongr
    have htailD : ∀ p ∈ primeBand n W,
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound Cmax n)),
          (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r)) ≤
          tail n * (1 / (p : ℝ)) ^ 2 := by
      intro p hp
      calc
        _ ≤ Gf * ((2 * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
          simpa only [actualExponentCutoff] using htailDn p hp
        _ = (2 * Gf * (K ^ 2 / Y ^ 2)) *
            (1 / (p : ℝ)) ^ 2 := by dsimp only [K, Y]; ring
        _ ≤ _ := by gcongr
    have htailRow : ∀ p ∈ primeBand n W,
        (p : ℝ) *
          ((∑ q ∈ (primeBand n W).erase p,
              (((∑ r ∈ highExponents
                    (valuationCutoff p (physicalBound Cmax n)),
                    eJI Gf n p q r)) +
                (∑ s ∈ highExponents
                    (valuationCutoff q (physicalBound Cmax n)),
                    eIJ Gf n p q s) +
                (∑ r ∈ highExponents
                    (valuationCutoff p (physicalBound Cmax n)),
                  ∑ s ∈ highExponents
                    (valuationCutoff q (physicalBound Cmax n)),
                    eJJ Gf n p q r s))) +
            3 * (∑ r ∈ highExponents
                (valuationCutoff p (physicalBound Cmax n)),
              (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r))) ≤ tail n := by
      intro p hp
      simpa only [actualExponentCutoff, tail] using htailRown p hp
    have htail0 : 0 ≤ tail n := by
      dsimp only [tail]
      exact tailRowMajorant_nonneg hGf hW hn
    have hmix := sigmaMixture_primePowerTransferBounds_of_common_profiles
      hkernel hCK.le (hhalf0 n) (by norm_num) (by norm_num) hGf
      htail0 htail0 htail0 htail0 weight law hn hW
      hpairProfile hsingleProfile hfallback htailJI htailIJ htailJJ
      htailD htailRow hbandTn
    have hmono := hmix.mono_epsilon (le_abs_self (rawRemainder n))
    simpa only [C_pow, rawRemainder, Eagg, tail, law, baseLaw,
      epsilon_BW] using hmono
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨epsilon_BW, hepsilon_BW0, hepsilon_BWT, hepsilon_BWRate, N₀, ?_⟩
  intro n eta hn heta
  exact hN₀ n hn eta heta

end

end Erdos390.Full.FixedFiniteMixtureFullUniform

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal001_001.{u_1} := by
  exact @Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer
