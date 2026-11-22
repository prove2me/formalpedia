-- Prove2me | solution 1 for Erdos390.Full.PaperRawTiltedValuationMeanRows.exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:17:56.537413+00:00
-- url     : https://prove2.me/submissions/209fba9b-de31-4fa5-9670-897ab701ca9f

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
import Theorems.Thm_Erdos390_Full_FixedFiniteMixtureSignedSquarefree_exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound


section
universe u_1
theorem Erdos390.Full.FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos : Erdos390.RemainingAnalyticGoal001_003.{u_1} := @Erdos390.Full.FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos_compact
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































end

end Erdos390.Full.PaperPrimePowerChamberError

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

/-- The chamber single-prime weight has a uniform geometric sum beginning
at exponent one. -/
theorem sum_singleWeight_positiveExponents_le
    {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ positiveExponents R, singleWeight p r) ≤
      6 / (p : ℝ) := by
  by_cases hR : 1 ≤ R
  · have hset : positiveExponents R =
        insert 1 (Finset.Icc 2 R) := by
      ext r
      simp only [positiveExponents, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    have htail := sum_raddone_inv_pow_le (p := p) (R := R) hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := zero_lt_two.trans_le hpR
    have hsq : 8 / (p : ℝ) ^ 2 ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hp0).2
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hpR)]
    calc
      singleWeight p 1 + ∑ x ∈ Finset.Icc 2 R, singleWeight p x =
          2 / (p : ℝ) +
            ∑ x ∈ Finset.Icc 2 R,
              (((x : ℝ) + 1) / (p : ℝ) ^ x) := by
        unfold singleWeight
        norm_num
      _ ≤ 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 :=
        add_le_add le_rfl htail
      _ ≤ 2 / (p : ℝ) + 4 / (p : ℝ) :=
        add_le_add le_rfl hsq
      _ = 6 / (p : ℝ) := by ring
  · have hR0 : R = 0 := by omega
    subst R
    simp [positiveExponents]
    positivity

variable {Cell : Type*} [Fintype Cell]

/-- Fixed-finite raw component means agree at the sharp reciprocal rate.
The coefficient box is arbitrary after `W`; all box dependence is confined
to the rate and eventual threshold. -/
theorem exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hC_le : ∀ c, C c ≤ Cmax)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ p ∈ (H c).primes, p ≤ W)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := fun c ↦ structuredCell (H c)
          (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
        ∀ hS : ∀ c, (S c).Nonempty, ∀ c c' : Cell,
          |((uniformOnFinset (S c) (hS c)).exponentialTilt
                (fun m : S c ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
              (fun m ↦ valuation p (m : ℕ)) -
            ((uniformOnFinset (S c') (hS c')).exponentialTilt
                (fun m : S c' ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
              (fun m ↦ valuation p (m : ℕ))| ≤
            epsilon n / (p : ℝ) := by
  obtain ⟨signedError, hsigned0, _hsignedT, hsignedRate,
    Nprofile, hprofileAll⟩ :=
      exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
        H A C Cmax hA hAC hC hC_le W hW
          hHeadLe
          B hB
  have hfallbackExists : ∀ c, ∃ Gc : ℝ, 0 < Gc ∧ ∃ Nc : ℕ,
      ∀ {n : ℕ} (eta : ℕ → ℝ), Nc ≤ n →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n) hS
          (primeBand n W) eta (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ Gc / (D : ℝ) := by
    intro c
    exact exists_uniform_fullTilt_primePower_fallback
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose Gcell hGcellData using hfallbackExists
  have hGcell (c : Cell) : 0 < Gcell c := (hGcellData c).1
  choose NfallbackCell hfallbackCell using fun c ↦ (hGcellData c).2
  let Gf : ℝ := ∑ c, Gcell c
  let Nfallback : ℕ := ∑ c, NfallbackCell c
  have hGf0 : 0 ≤ Gf := by
    dsimp only [Gf]
    exact Finset.sum_nonneg fun c hc ↦ (hGcell c).le
  have hGcellLe (c : Cell) : Gcell c ≤ Gf := by
    dsimp only [Gf]
    exact Finset.single_le_sum
      (fun d hd ↦ (hGcell d).le) (Finset.mem_univ c)
  let tailCoefficient : ℕ → ℝ := fun n ↦ 4 * Gf / L n
  let epsilon : ℕ → ℝ := fun n ↦ 12 * signedError n + tailCoefficient n
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLdivL : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have htailRate : Tendsto (fun n : ℕ ↦
      tailCoefficient n * Real.log (L n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ 4 * Gf)
        atTop (nhds (4 * Gf)) := tendsto_const_nhds
    have hmul := hconst.mul hlogLdivL
    have hmul0 : Tendsto (fun n : ℕ ↦
        (4 * Gf) * (Real.log (L n) / L n)) atTop (nhds 0) := by
      simpa only [mul_zero] using hmul
    apply hmul0.congr'
    filter_upwards with n
    dsimp only [tailCoefficient]
    ring
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsignedConst : Tendsto (fun n : ℕ ↦
        12 * (signedError n * Real.log (L n))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hsignedRate
    have hsum := hsignedConst.add htailRate
    have hsum0 : Tendsto (fun n : ℕ ↦
        12 * (signedError n * Real.log (L n)) +
          tailCoefficient n * Real.log (L n)) atTop (nhds 0) := by
      simpa only [zero_add] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [epsilon]
    ring
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    cases n with
    | zero => simp [epsilon, tailCoefficient, L, hsigned0]
    | succ n =>
      dsimp only [epsilon, tailCoefficient]
      have hL0 : 0 ≤ L (n + 1) := by
        exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      exact add_nonneg
        (mul_nonneg (by norm_num) (hsigned0 (n + 1)))
        (div_nonneg (mul_nonneg (by norm_num) hGf0) hL0)
  obtain ⟨q₀, q₁, aux, _hq₀, _hq₁, _hWq₀, _hq₀q₁,
    _hauxDef, hauxEvent⟩ := exists_eventually_auxiliaryPrime W
  have htailSharp := eventually_mul_two_div_yNat_pow_four_le_sharp
  have hgood : ∀ᶠ n : ℕ in atTop,
      (q₀ ∈ primeBand n W ∧ q₁ ∈ primeBand n W ∧
        ∀ p ∈ primeBand n W, aux p ∈ (primeBand n W).erase p) ∧
      (∀ p : ℕ, 0 < p → p ≤ yNat n → ∀ G : ℝ, 0 ≤ G →
        G * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) ≤
          ((2 * G) / L n) * (1 / (p : ℝ))) ∧
      1 < n := by
    filter_upwards [hauxEvent, htailSharp, Filter.eventually_gt_atTop 1]
      with n haux htail hn
    exact ⟨haux, htail, hn⟩
  obtain ⟨Ngood, hNgood⟩ := Filter.eventually_atTop.mp hgood
  refine ⟨epsilon, hepsilon0, hepsilonRate,
    max Nprofile (max Nfallback Ngood), ?_⟩
  intro n p eta hN hpBand heta
  have hNprofile : Nprofile ≤ n := by omega
  have hNfallback : Nfallback ≤ n := by omega
  have hNgoodBound : Ngood ≤ n := by omega
  obtain ⟨⟨hq₀Band, hq₁Band, haux⟩, htailSharpN, hn⟩ :=
    hNgood n hNgoodBound
  let S := fun c ↦ structuredCell (H c)
    (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
  change ∀ hS : ∀ c, (S c).Nonempty, ∀ c c' : Cell, _
  intro hS c c'
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hTpos : 0 < yNat n ^ 4 := pow_pos (hp.pos.trans_le hpY) 4
  let Kcut : ℕ := Nat.log p (yNat n ^ 4)
  let main : ℕ → ℝ := fun k ↦ paperDivisibilityMain n (p ^ k)
  let mainSum : ℝ := ∑ k ∈ positiveExponents Kcut, main k
  have hprofiles := (hprofileAll eta hNprofile heta).2 hS
  have hpairProfile := hprofiles.1
  have hqErase : aux p ∈ (primeBand n W).erase p := haux p hpBand
  have hprofileOne (d : Cell) (k : ℕ)
      (hk : k ∈ positiveExponents Kcut) :
      |((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| ≤
        signedError n * singleWeight p k := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hpK : p ^ Kcut ≤ yNat n ^ 4 :=
      Nat.pow_log_le_self p hTpos.ne'
    have hpk : p ^ k ≤ yNat n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hraw := hpairProfile d p hpBand (aux p) hqErase k 0
      (by simpa only [pairPower, pow_zero, mul_one] using hpk)
    simpa only [S, main, pairPower, pow_zero, mul_one,
      pairWeight_eq_single_mul, singleWeight, Nat.cast_zero, zero_add,
      div_one, mul_one,
      PrimePowerCovariance.BoundedValuationLaw.widen_probability,
      PrimePowerCovariance.BoundedValuationLaw.widen_value,
      StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hraw
  have htailOne (d : Cell) :
      |((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut,
              divInd (p ^ k) (m : ℕ))| ≤
        ((2 * Gf) / L n) * (1 / (p : ℝ)) := by
    have hNcell : NfallbackCell d ≤ n := by
      have hd : NfallbackCell d ≤ Nfallback := by
        dsimp only [Nfallback]
        exact Finset.single_le_sum
          (fun e he ↦ Nat.zero_le (NfallbackCell e)) (Finset.mem_univ d)
      exact hd.trans hNfallback
    have hdivCell := hfallbackCell d eta hNcell heta (hS d)
    have hdiv (D : ℕ) (hD : 0 < D) :
        ((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ divInd D (m : ℕ)) ≤ Gf * (1 / (D : ℝ)) := by
      have hraw := hdivCell D hD
      have hmono := div_le_div_of_nonneg_right (hGcellLe d)
        (by positivity : (0 : ℝ) ≤ (D : ℝ))
      simpa only [S, valuationTilt_probability, valuationTilt_value,
        one_mul, div_eq_mul_inv] using hraw.trans hmono
    have hvaluePos : ∀ m : S d, 0 < (m : ℕ) := by
      intro m
      exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
    have hvalueLe : ∀ m : S d, (m : ℕ) ≤ physicalBound (C d) n := by
      intro m
      exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
    have hraw :=
      PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback_unrestricted
        ((uniformOnFinset (S d) (hS d)).exponentialTilt
          (fun m : S d ↦
            valuationScore (primeBand n W) eta (L n) (m : ℕ)))
        (fun m : S d ↦ (m : ℕ)) hp hvaluePos hvalueLe hGf0 hdiv
        (Kcut := Kcut)
    have hpowNat : yNat n ^ 4 < p ^ (Kcut + 1) := by
      simpa only [Kcut, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self hp.one_lt (yNat n ^ 4)
    have hpow : ((yNat n ^ 4 : ℕ) : ℝ) ≤
        (p : ℝ) ^ (Kcut + 1) := by exact_mod_cast hpowNat.le
    have hTreal : (0 : ℝ) < (yNat n ^ 4 : ℕ) := by exact_mod_cast hTpos
    have hrecip : 2 / (p : ℝ) ^ (Kcut + 1) ≤
        2 / ((yNat n ^ 4 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hTreal hpow
    calc
      _ ≤ Gf * (2 / (p : ℝ) ^ (Kcut + 1)) := hraw
      _ ≤ Gf * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip hGf0
      _ ≤ ((2 * Gf) / L n) * (1 / (p : ℝ)) :=
        htailSharpN p hp.pos hpY Gf hGf0
  have hsumWeight : (∑ k ∈ positiveExponents Kcut,
      singleWeight p k) ≤ 6 / (p : ℝ) :=
    sum_singleWeight_positiveExponents_le hp.two_le
  have hcomponent (d : Cell) :
      |((uniformOnFinset (S d) (hS d)).exponentialTilt
            (fun m : S d ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ)) - mainSum| ≤
        (6 * signedError n + 2 * Gf / L n) * (1 / (p : ℝ)) := by
    let mu := (uniformOnFinset (S d) (hS d)).exponentialTilt
      (fun m : S d ↦ valuationScore (primeBand n W) eta (L n) (m : ℕ))
    let trunc : S d → ℝ := fun m ↦
      ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ)
    let tail : S d → ℝ := fun m ↦ valuation p (m : ℕ) - trunc m
    have hexpect : mu.expect (fun m ↦ valuation p (m : ℕ)) =
        mu.expect trunc + mu.expect tail := by
      have hpoint : (fun m : S d ↦ (valuation p (m : ℕ) : ℝ)) =
          fun m ↦ trunc m + tail m := by
        funext m
        dsimp only [tail]
        ring
      rw [hpoint, mu.expect_add]
    have htruncExpand : mu.expect trunc =
        ∑ k ∈ positiveExponents Kcut,
          mu.expect (fun m ↦ divInd (p ^ k) (m : ℕ)) := by
      exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
        (positiveExponents Kcut) (fun k m ↦ divInd (p ^ k) (m : ℕ))
    have htrunc : |mu.expect trunc - mainSum| ≤
        signedError n * (6 / (p : ℝ)) := by
      rw [htruncExpand]
      dsimp only [mainSum]
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ k ∈ positiveExponents Kcut,
            (mu.expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k)| ≤
          ∑ k ∈ positiveExponents Kcut,
            |mu.expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ positiveExponents Kcut,
            signedError n * singleWeight p k := by
          exact Finset.sum_le_sum fun k hk ↦ by
            simpa only [mu] using hprofileOne d k hk
        _ = signedError n *
            (∑ k ∈ positiveExponents Kcut, singleWeight p k) := by
          rw [Finset.mul_sum]
        _ ≤ signedError n * (6 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumWeight (hsigned0 n)
    have htail : |mu.expect tail| ≤
        ((2 * Gf) / L n) * (1 / (p : ℝ)) := by
      simpa only [mu, tail, trunc] using htailOne d
    rw [hexpect]
    calc
      |mu.expect trunc + mu.expect tail - mainSum| =
          |(mu.expect trunc - mainSum) + mu.expect tail| := by ring_nf
      _ ≤ |mu.expect trunc - mainSum| + |mu.expect tail| := abs_add_le _ _
      _ ≤ signedError n * (6 / (p : ℝ)) +
          ((2 * Gf) / L n) * (1 / (p : ℝ)) :=
        add_le_add htrunc htail
      _ = (6 * signedError n + 2 * Gf / L n) *
          (1 / (p : ℝ)) := by ring
  calc
    _ ≤ |((uniformOnFinset (S c) (hS c)).exponentialTilt
            (fun m : S c ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ)) - mainSum| +
        |((uniformOnFinset (S c') (hS c')).exponentialTilt
            (fun m : S c' ↦
              valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
          (fun m ↦ valuation p (m : ℕ)) - mainSum| := by
      have htri := abs_sub
        (((uniformOnFinset (S c) (hS c)).exponentialTilt
            (fun m : S c ↦ valuationScore (primeBand n W) eta (L n)
              (m : ℕ))).expect (fun m ↦ valuation p (m : ℕ)) - mainSum)
        (((uniformOnFinset (S c') (hS c')).exponentialTilt
            (fun m : S c' ↦ valuationScore (primeBand n W) eta (L n)
              (m : ℕ))).expect (fun m ↦ valuation p (m : ℕ)) - mainSum)
      simpa only [sub_sub_sub_cancel_right] using htri
    _ ≤ (6 * signedError n + 2 * Gf / L n) * (1 / (p : ℝ)) +
        (6 * signedError n + 2 * Gf / L n) * (1 / (p : ℝ)) :=
      add_le_add (hcomponent c) (hcomponent c')
    _ = 2 * ((6 * signedError n + 2 * Gf / L n) *
        (1 / (p : ℝ))) := by ring
    _ = epsilon n / (p : ℝ) := by
      dsimp only [epsilon, tailCoefficient]
      ring

end

end Erdos390.Full.PaperRawTiltedValuationMeanRows

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal004_008.{u_1} := by
  exact @Erdos390.Full.PaperRawTiltedValuationMeanRows.exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate
