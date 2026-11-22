-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:26:50.983826+00:00
-- url     : https://prove2.me/submissions/c6428895-6856-4946-a1f4-f675aaadb8ce

import Definitions.Def_erdos390_remaining_analytic_propositions_007
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
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_uniformAverage_divInd_paper_bound

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

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/



















































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

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



end

end Erdos390.Full.ValuationScoreDomination

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

/- Source module: Erdos390.Full.PaperPrimePowerTailRate -/
section


/-!
# The elementary `p L / yNat^4` tail rate

The valuation cutoff used in the nuisance estimates is `T = yNat n ^ 4`.
For every active prime `p <= yNat n`, its omitted tail becomes negligible
on the sharp `1 / (p L)` scale because `p L / T -> 0` uniformly in `p`.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerTailRate

open ArithmeticModel Scale

noncomputable section

theorem tendsto_L_div_three_fifths :
    Tendsto (fun n : ℕ ↦
      L n / (n : ℝ) ^ (3 / 5 : ℝ)) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x / x ^ (3 / 5 : ℝ))
      atTop (𝓝 0) := by
    simpa using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 3 / 5)).tendsto_div_nhds_zero
  simpa only [L, Real.rpow_one] using
    hreal.comp tendsto_natCast_atTop_atTop

/-- The integral smoothness cutoff is eventually at least `n^(1/5)`.
This deliberately uses only the already-proved logarithmic lower bound for
`yNat`; no informal floor comparison is hidden. -/
theorem eventually_rpow_one_fifth_le_yNat :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 5 : ℝ) ≤ (yNat n : ℝ) := by
  filter_upwards [FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    Filter.eventually_gt_atTop 1] with n hlog hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hlogYpos : 0 < Real.log (yNat n : ℝ) := by
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : (0 : ℝ) < (yNat n : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogYpos |>.trans' zero_lt_one
  calc
    (n : ℝ) ^ (1 / 5 : ℝ) =
        Real.exp ((1 / 5 : ℝ) * L n) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      unfold L
      ring
    _ ≤ Real.exp (Real.log (yNat n : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (yNat n : ℝ) := Real.exp_log hYpos

/-- Uniform arithmetic tail comparison in the exact form needed after the
logarithmic valuation cutoff. -/
theorem eventually_prime_mul_L_div_yNat_pow_four_le_one :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p ≤ yNat n →
      (p : ℝ) * L n / (yNat n : ℝ) ^ 4 ≤ 1 := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      L n / (n : ℝ) ^ (3 / 5 : ℝ) ≤ 1 :=
    (tendsto_L_div_three_fifths.eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [eventually_rpow_one_fifth_le_yNat, hratio,
    FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    Filter.eventually_gt_atTop 1] with n hY hratioN hlog hn
  intro p hp
  let Y : ℝ := yNat n
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hlogYpos : 0 < Real.log Y := by
    dsimp only [Y]
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : 0 < Y :=
    (Real.log_pos_iff (by dsimp only [Y]; positivity)).mp hlogYpos |>.trans'
      zero_lt_one
  have hpY : (p : ℝ) ≤ Y := by
    dsimp only [Y]
    exact_mod_cast hp
  have hnPowPos : 0 < (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hY3 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ Y ^ 3 := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 5 : ℝ))
      (by simpa only [Y] using hY) (by norm_num : (0 : ℝ) ≤ 3)
    calc
      (n : ℝ) ^ (3 / 5 : ℝ) =
          ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (3 : ℝ) := by
        convert Real.rpow_mul (Nat.cast_nonneg n) (1 / 5 : ℝ) (3 : ℝ)
          using 1
        all_goals norm_num
      _ ≤ Y ^ (3 : ℝ) := hmono
      _ = Y ^ 3 := by norm_num [Real.rpow_natCast]
  calc
    (p : ℝ) * L n / Y ^ 4 ≤ Y * L n / Y ^ 4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpY hL.le) (by positivity)
    _ = L n / Y ^ 3 := by field_simp [hYpos.ne']
    _ ≤ L n / (n : ℝ) ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left hL.le hnPowPos hY3
    _ ≤ 1 := hratioN

/-- Direct sharp-rate conversion used with the valuation-tail census. -/
theorem eventually_mul_two_div_yNat_pow_four_le_sharp :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p → p ≤ yNat n →
      ∀ G : ℝ, 0 ≤ G →
        G * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) ≤
          ((2 * G) / L n) * (1 / (p : ℝ)) := by
  filter_upwards [eventually_prime_mul_L_div_yNat_pow_four_le_one,
    Filter.eventually_gt_atTop 1,
    FriableAsymptotic.eventually_one_fifth_L_le_log_yNat] with
      n hrate hn hlog
  intro p hp hpY G hG
  have hL : 0 < L n := L_pos hn
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogYpos : 0 < Real.log (yNat n : ℝ) := by
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : (0 : ℝ) < (yNat n : ℝ) :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogYpos)
  have hcoef : 0 ≤ (2 * G) / ((p : ℝ) * L n) := by positivity
  calc
    G * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) =
        ((2 * G) / ((p : ℝ) * L n)) *
          (((p : ℝ) * L n) / ((yNat n : ℝ) ^ 4)) := by
      norm_num only [Nat.cast_pow]
      field_simp [hpR.ne', hL.ne', hYpos.ne']
    _ ≤ ((2 * G) / ((p : ℝ) * L n)) * 1 :=
      mul_le_mul_of_nonneg_left (hrate p hpY) hcoef
    _ = ((2 * G) / L n) * (1 / (p : ℝ)) := by ring

end

end Erdos390.Full.PaperPrimePowerTailRate

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

/-- A reciprocal divisor bound controls the literal valuation tail beyond
an arbitrary exponent cutoff.  This is a finite theorem: the valuation is
first expanded only up to the common endpoint `M`, and the remaining finite
geometric sum is then bounded by its infinite tail. -/
theorem abs_expect_valuation_sub_cutoff_le_of_divisor_fallback
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    {M p Kcut : ℕ} {G : ℝ}
    (hp : p.Prime) (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M) (hcut : Kcut ≤ M)
    (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      mu.expect (fun omega ↦ divInd D (value omega)) ≤
        G * (1 / (D : ℝ))) :
    |mu.expect (fun omega ↦
        valuation p (value omega) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (value omega))| ≤
      G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
  have hsplit (f : ℕ → ℝ) :
      (∑ k ∈ positiveExponents M, f k) =
        (∑ k ∈ positiveExponents Kcut, f k) +
          ∑ k ∈ Icc (Kcut + 1) M, f k := by
    have hsets : Icc 1 M = Icc 1 Kcut ∪ Icc (Kcut + 1) M := by
      ext k
      simp only [mem_Icc, mem_union]
      omega
    have hdisjoint : Disjoint (Icc 1 Kcut) (Icc (Kcut + 1) M) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [mem_Icc] at hk hk'
      omega
    unfold positiveExponents
    rw [hsets, Finset.sum_union hdisjoint]
  have hpoint :
      (fun omega ↦ valuation p (value omega) -
        ∑ k ∈ positiveExponents Kcut,
          divInd (p ^ k) (value omega)) =
      fun omega ↦ ∑ k ∈ Icc (Kcut + 1) M,
        divInd (p ^ k) (value omega) := by
    funext omega
    rw [valuation_eq_sum_divInd_of_le hp
      (hvaluePos omega) (hvalueLe omega), hsplit]
    ring
  have hterm0 (k : ℕ) :
      0 ≤ mu.expect (fun omega ↦ divInd (p ^ k) (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg _ _)
  rw [hpoint, PrimePowerCutoffCovariance.FiniteProbability.expect_sum]
  rw [abs_of_nonneg (Finset.sum_nonneg fun k hk ↦ hterm0 k)]
  calc
    (∑ k ∈ Icc (Kcut + 1) M,
        mu.expect (fun omega ↦ divInd (p ^ k) (value omega))) ≤
      ∑ k ∈ Icc (Kcut + 1) M,
        G * (1 / ((p ^ k : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hdiv (p ^ k) (pow_pos hp.pos k)
    _ = G * (∑ k ∈ Icc (Kcut + 1) M,
        1 / ((p ^ k : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
          exact mul_le_mul_of_nonneg_left
            (LocalFugacityBounds.sum_inv_pow_tail_le
              (p := p) (r := Kcut) (A := M) hp.two_le) hG

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

/- Source module: Erdos390.Full.PaperRawTiltedValuationMeanRows -/
section


/-!
# Raw tilted full-valuation component-mean agreement

The common four-mark profile is summed only through
`Nat.log p (yNat n ^ 4)`.  The arbitrary-divisor fallback controls the
literal remaining valuation tail.  This produces the sharp
`epsilon(n)/p`, `epsilon(n) log L(n) -> 0` component-mean row needed for the
head nuisance coordinate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperRawTiltedValuationMeanRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open StructuredCellValuationLaw ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPrimePowerFallback
open PaperPrimePowerChamberError PaperScaleMarkedCell
open FixedFiniteMixtureFullUniform FixedFiniteMixtureSignedSquarefree
open PaperPrimePowerAuxiliaryPrime PaperPrimePowerTailRate
open LocalFugacityBounds

noncomputable section

set_option maxHeartbeats 2400000

/-- The finite full-valuation tail estimate remains true without assuming
that the chosen exponent cutoff is below the ambient endpoint.  If the
cutoff is larger, the valuation expansion already terminates and the tail
is identically zero. -/
theorem PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback_unrestricted
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    {M p Kcut : ℕ} {G : ℝ}
    (hp : p.Prime) (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      mu.expect (fun omega ↦ divInd D (value omega)) ≤
        G * (1 / (D : ℝ))) :
    |mu.expect (fun omega ↦
        valuation p (value omega) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (value omega))| ≤
      G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
  by_cases hcut : Kcut ≤ M
  · exact PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback
      mu value hp hvaluePos hvalueLe hcut hG hdiv
  · have hMK : M ≤ Kcut := (Nat.lt_of_not_ge hcut).le
    have hpoint : (fun omega ↦
        valuation p (value omega) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (value omega)) = fun _ ↦ 0 := by
      funext omega
      rw [valuation_eq_sum_divInd_of_le hp (hvaluePos omega)
        ((hvalueLe omega).trans hMK)]
      ring
    rw [hpoint]
    have hzero : mu.expect (fun _ ↦ (0 : ℝ)) = 0 := by
      exact mu.expect_zero
    rw [hzero, abs_zero]
    positivity



variable {Cell : Type*} [Fintype Cell]



end

end Erdos390.Full.PaperRawTiltedValuationMeanRows

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure -/
section


/-!
# Sharp valuation-rate ingredients for the smooth source

This file begins the analytic lift left explicit by
`BankPaperCanonicalSmoothSourceGuardedRateClosure`.

The first theorem below is the sharp un-tilted full-valuation profile for one
fixed raw structured cell.  It is obtained only from already proved inputs:

* the common `paperDivisibilityMain` law through `yNat n ^ 4`;
* the arbitrary-divisor reciprocal fallback;
* the finite prime-power tail identity; and
* the sharp conversion of the `yNat n ^ 4` tail to `1 / (p * L n)`.

No full-valuation comparison is assumed.
-/

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawPrefixThirdCumulantFallback
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.GuardedUniformCell
open Erdos390.Full.GuardDeletionSquarefreeProfiles
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperCanonicalTiltedPrefixRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Fixed raw structured cells -/

/-- The genuine full valuation on one fixed raw structured cell has the
common truncated Dickman profile with the sharp `1 / (p * L)` error.

The returned nonemptiness witness is produced by the marked-cell theorem;
it is not an additional premise. -/
theorem
    exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
    (P : Pattern) {A C : Real}
    (hA : 0 < A) (hAC : A < C) (hC : 0 < C)
    (W : Nat) (_hW : 1 < W)
    (hHeadLe : ∀ q ∈ P.primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let S := structuredCell P
          (physicalBound A n) (physicalBound C n) (yNat n)
        let Kcut := Nat.log p (yNat n ^ 4)
        ∃ hS : S.Nonempty,
          |(uniformOnFinset S hS).expect
                (fun m ↦ valuation p (m : Nat)) -
            ∑ k ∈ positiveExponents Kcut,
              paperDivisibilityMain n (p ^ k)| ≤
            Cval / ((p : Real) * L n) := by
  obtain ⟨K, hK, Nprofile, hprofile⟩ :=
    PaperScaleMarkedCell.exists_uniform_uniformAverage_divInd_paper_bound
      P hA hAC
  obtain ⟨G, hG, Nfallback, hfallback⟩ :=
    PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_divInd_fallback
      P hA hAC hC
  have htailSharp :=
    PaperPrimePowerTailRate.eventually_mul_two_div_yNat_pow_four_le_sharp
  have hgood : ∀ᶠ n : Nat in atTop,
      (∀ p : Nat, 0 < p → p ≤ yNat n → ∀ H : Real, 0 ≤ H →
        H * (2 / ((yNat n ^ 4 : Nat) : Real)) ≤
          ((2 * H) / L n) * (1 / (p : Real))) ∧
      1 < n := by
    filter_upwards [htailSharp, Filter.eventually_gt_atTop 1]
      with n htail hn
    exact ⟨htail, hn⟩
  obtain ⟨Ngood, hNgood⟩ := Filter.eventually_atTop.mp hgood
  let Cval : Real := 2 * K + 2 * G
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    positivity
  refine ⟨Cval, hCval, max Nprofile (max Nfallback Ngood), ?_⟩
  intro n p hN hpBand
  dsimp only
  have hNprofile : Nprofile ≤ n := by omega
  have hNfallback : Nfallback ≤ n := by omega
  have hNgoodBound : Ngood ≤ n := by omega
  obtain ⟨htailSharpN, hn⟩ := hNgood n hNgoodBound
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hp4 : p ≤ yNat n ^ 4 :=
    hpY.trans (Nat.le_pow (by omega : 0 < 4))
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (Nat.lt_succ_of_le hpY)
  have hpHead : Nat.Coprime p P.modulus :=
    PaperPrimePowerAuxiliaryPrime.coprime_modulus_of_mem_primeBand_of_headSupport
      P hHeadLe hpBand
  let S := structuredCell P
    (physicalBound A n) (physicalBound C n) (yNat n)
  let Kcut : Nat := Nat.log p (yNat n ^ 4)
  let main : Nat → Real := fun k ↦
    paperDivisibilityMain n (p ^ k)
  let mainSum : Real := ∑ k ∈ positiveExponents Kcut, main k
  have hprofileP :=
    hprofile (n := n) (d := p) hNprofile hp.pos hp4 hpSmooth hpHead
  have hS : S.Nonempty := by
    simpa only [S] using hprofileP.1
  refine ⟨hS, ?_⟩
  let mu := uniformOnFinset S hS
  let trunc : S → Real := fun m ↦
    ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : Nat)
  let tail : S → Real := fun m ↦ valuation p (m : Nat) - trunc m
  have hprofilePower (k : Nat)
      (hk : k ∈ positiveExponents Kcut) :
      |mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) - main k| ≤
        K / (((p ^ k : Nat) : Real) * L n) := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hY4pos : 0 < yNat n ^ 4 :=
      pow_pos (hp.pos.trans_le hpY) 4
    have hpK : p ^ Kcut ≤ yNat n ^ 4 :=
      Nat.pow_log_le_self p hY4pos.ne'
    have hpk4 : p ^ k ≤ yNat n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hpkSmooth := StructuredCells.pow_mem_smoothNumbers hpSmooth k
    have hpkHead := hpHead.pow_left k
    have hraw :=
      (hprofile (n := n) (d := p ^ k) hNprofile
        (pow_pos hp.pos k) hpk4 hpkSmooth hpkHead).2
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    simpa only [S, mu, main] using hraw
  have hdiv (D : Nat) (hD : 0 < D) :
      mu.expect (fun m ↦ divInd D (m : Nat)) ≤
        G * (1 / (D : Real)) := by
    have hraw := hfallback hNfallback hS D hD
    simpa only [S, mu, div_eq_mul_inv, one_mul] using hraw
  have hvaluePos : ∀ m : S, 0 < (m : Nat) := by
    intro m
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hvalueLe : ∀ m : S, (m : Nat) ≤ physicalBound C n := by
    intro m
    exact
      (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have htailRaw :=
    PaperRawTiltedValuationMeanRows.PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback_unrestricted
        mu (fun m : S ↦ (m : Nat)) hp hvaluePos hvalueLe hG.le hdiv
        (Kcut := Kcut)
  have hpowNat : yNat n ^ 4 < p ^ (Kcut + 1) := by
    simpa only [Kcut, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hp.one_lt (yNat n ^ 4)
  have hpow : ((yNat n ^ 4 : Nat) : Real) ≤
      (p : Real) ^ (Kcut + 1) := by
    exact_mod_cast hpowNat.le
  have hY4real : (0 : Real) < (yNat n ^ 4 : Nat) := by
    exact_mod_cast pow_pos (hp.pos.trans_le hpY) 4
  have hrecip : 2 / (p : Real) ^ (Kcut + 1) ≤
      2 / ((yNat n ^ 4 : Nat) : Real) :=
    div_le_div_of_nonneg_left (by norm_num) hY4real hpow
  have htail :
      |mu.expect tail| ≤ ((2 * G) / L n) * (1 / (p : Real)) := by
    have hfirst :
        |mu.expect (fun m ↦
            valuation p (m : Nat) -
              ∑ k ∈ positiveExponents Kcut,
                divInd (p ^ k) (m : Nat))| ≤
          G * (2 / (p : Real) ^ (Kcut + 1)) := by
      exact htailRaw
    calc
      |mu.expect tail| ≤
          G * (2 / (p : Real) ^ (Kcut + 1)) := by
        simpa only [tail, trunc] using hfirst
      _ ≤ G * (2 / ((yNat n ^ 4 : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left hrecip hG.le
      _ ≤ ((2 * G) / L n) * (1 / (p : Real)) :=
        htailSharpN p hp.pos hpY G hG.le
  have hsumReciprocal :
      (∑ k ∈ positiveExponents Kcut,
          1 / (((p ^ k : Nat) : Real))) ≤
        2 / (p : Real) :=
    sum_inv_prime_powers_le p Kcut hp.two_le
  have htruncExpand :
      mu.expect trunc =
        ∑ k ∈ positiveExponents Kcut,
          mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) := by
    exact
      PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
        (positiveExponents Kcut)
        (fun k m ↦ divInd (p ^ k) (m : Nat))
  have htrunc :
      |mu.expect trunc - mainSum| ≤
        ((2 * K) / L n) * (1 / (p : Real)) := by
    rw [htruncExpand]
    dsimp only [mainSum]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ positiveExponents Kcut,
          (mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) - main k)| ≤
        ∑ k ∈ positiveExponents Kcut,
          |mu.expect (fun m ↦ divInd (p ^ k) (m : Nat)) - main k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ positiveExponents Kcut,
          K / (((p ^ k : Nat) : Real) * L n) := by
        exact Finset.sum_le_sum fun k hk ↦ hprofilePower k hk
      _ = (K / L n) *
          (∑ k ∈ positiveExponents Kcut,
            1 / (((p ^ k : Nat) : Real))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ ≤ (K / L n) * (2 / (p : Real)) := by
        exact mul_le_mul_of_nonneg_left hsumReciprocal
          (div_nonneg hK.le (L_pos hn).le)
      _ = ((2 * K) / L n) * (1 / (p : Real)) := by ring
  have hexpect :
      mu.expect (fun m ↦ valuation p (m : Nat)) =
        mu.expect trunc + mu.expect tail := by
    have hpoint : (fun m : S ↦ (valuation p (m : Nat) : Real)) =
        fun m ↦ trunc m + tail m := by
      funext m
      dsimp only [tail]
      ring
    rw [hpoint, mu.expect_add]
  change
    |mu.expect (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      Cval / ((p : Real) * L n)
  rw [hexpect]
  calc
    |mu.expect trunc + mu.expect tail - mainSum| =
        |(mu.expect trunc - mainSum) + mu.expect tail| := by ring_nf
    _ ≤ |mu.expect trunc - mainSum| + |mu.expect tail| :=
      abs_add_le _ _
    _ ≤ ((2 * K) / L n) * (1 / (p : Real)) +
        ((2 * G) / L n) * (1 / (p : Real)) :=
      add_le_add htrunc htail
    _ = Cval / ((p : Real) * L n) := by
      dsimp only [Cval]
      field_simp [hpR.ne', (L_pos hn).ne']



/-! ## Literal guard deletion -/





/-! ## The concrete guard ledger at the stronger `1 / L` rate -/















end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal007_011 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
