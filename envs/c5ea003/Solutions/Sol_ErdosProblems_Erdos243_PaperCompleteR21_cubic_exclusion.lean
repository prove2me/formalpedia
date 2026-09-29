-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR21.cubic_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:27:17.883592+00:00
-- url     : https://prove2.me/submissions/2dd1a983-4df4-47fd-98be-5b613a5b4f75

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_CubicRateExclusionChain
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_lowerDensityAtLeast_iff_of_eventual_iff
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_zero_density_multiplier_irreducibility
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_zeroLowerDensity_iff_no_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_zero_density_primitive_shape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_primitive_cubic_zero_density_impossible_of_square_specialisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_transport_square
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Erdős 243: from the square specialisation to cubic-rate irrationality

Development file: the three paper environments downstream of
`long243:res:squarespec`, proved from that lemma taken as the hypothesis
`SquareSpecialisation`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20



/-- Evaluating the depressed cubic along any ring homomorphism out of `ℚ`. -/
theorem eval₂_cubicScalePolynomial {R : Type*} [CommRing R] (f : ℚ →+* R) (x : R) (η : ℚ) :
    Polynomial.eval₂ f x (cubicScalePolynomial η) = x ^ 3 - x + f η := by
  show Polynomial.eval₂ f x (Polynomial.X ^ 3 - Polynomial.X + Polynomial.C η) = _
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]

/-! ### `long243:res:transportsquare` -/





/-! ### `long243:res:cubicexclusion` -/
end ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR21 in
set_option maxHeartbeats 1000000 in

theorem solution (hss : SquareSpecialisation)
    (a C D : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hC : ∀ n, 0 < C n) (hD : ∀ n, 0 < D n)
    (hCrec : ∀ n, C (n + 1) = a n * C n - D n)
    (hDrec : ∀ n, D (n + 1) = a n * D n)
    (A B : ℚ) (hA : 0 < A) :
    (∃ dens : ℝ, 0 < dens ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        dens * (X : ℝ) ≤ (exceptionCount
          {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          (X + 1) : ℝ)) ∧
      ¬ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B := by
  classical
  set E : Set ℕ :=
    {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B} with hE
  have hcore : ¬ ZeroLowerDensity E := by
    intro hzero
    set aN : ℕ → ℕ := fun n => (a n).toNat with haN
    set CN : ℕ → ℕ := fun n => (C n).toNat with hCN
    set DN : ℕ → ℕ := fun n => (D n).toNat with hDN
    have haNc : ∀ n, ((aN n : ℤ)) = a n := fun n => Int.toNat_of_nonneg (ha n).le
    have hCNc : ∀ n, ((CN n : ℤ)) = C n := fun n => Int.toNat_of_nonneg (hC n).le
    have hDNc : ∀ n, ((DN n : ℤ)) = D n := fun n => Int.toNat_of_nonneg (hD n).le
    have hCNpos : ∀ n, 0 < CN n := by
      intro n
      have h1 := hC n
      have h2 := hCNc n
      omega
    have hDNpos : ∀ n, 0 < DN n := by
      intro n
      have h1 := hD n
      have h2 := hDNc n
      omega
    have hCNrec : ∀ n, CN (n + 1) + DN n = aN n * CN n := by
      intro n
      have h : ((CN (n + 1) + DN n : ℕ) : ℤ) = ((aN n * CN n : ℕ) : ℤ) := by
        push_cast
        rw [hCNc, hDNc, haNc, hCNc]
        linarith [hCrec n]
      exact_mod_cast h
    have hDNrec : ∀ n, DN (n + 1) = aN n * DN n := by
      intro n
      have h : ((DN (n + 1) : ℕ) : ℤ) = ((aN n * DN n : ℕ) : ℤ) := by
        push_cast
        rw [hDNc, haNc, hDNc]
        linarith [hDrec n]
      exact_mod_cast h
    have hsets :
        {n : ℕ | (CN n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B} = E := by
      ext n
      simp only [hE, Set.mem_setOf_eq]
      have hcast : ((CN n : ℕ) : ℚ) = ((C n : ℤ) : ℚ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (hCNc n)
      rw [hcast]
    have hzero' : ZeroLowerDensity
        {n : ℕ | (CN n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B} := by
      rw [hsets]; exact hzero
    obtain ⟨N, g, m, c, hg, hm, hc, hmcoeff, hccoeff, hprofile, htail⟩ :=
      rational_cubic_zero_density_primitive_shape aN CN DN A B hA hCNpos hDNpos hCNrec hDNrec
        hzero'
    set u : ℕ → ℕ := fun n => CN n / g with hu
    set v : ℕ → ℕ := fun n => DN n / g with hv
    set mN : ℕ := m.toNat with hmN
    have hmNc : ((mN : ℤ)) = m := Int.toNat_of_nonneg hm.le
    have hmNpos : 0 < mN := by omega
    have hgQ : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
    set F : Set ℕ := {n : ℕ | (u n : ℤ) ≠ (mN : ℤ) * risingBinomial n + c} with hF
    have heq : ∀ n, N ≤ n →
        (n ∈ {n : ℕ | (CN n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          ↔ n ∈ F) := by
      intro n hn
      obtain ⟨hgcd, -, -, -, -, -, -⟩ := htail n hn
      have hdvd : g ∣ CN n := hgcd ▸ Nat.gcd_dvd_left (CN n) (DN n)
      have hCg : (CN n : ℚ) = (g : ℚ) * ((u n : ℕ) : ℚ) := by
        simp only [hu]
        have h : g * (CN n / g) = CN n := Nat.mul_div_cancel' hdvd
        have h2 : ((g * (CN n / g) : ℕ) : ℚ) = ((CN n : ℕ) : ℚ) := by exact_mod_cast h
        rw [Nat.cast_mul] at h2
        exact h2.symm
      have hprof : A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B
          = (g : ℚ) * (((m * risingBinomial n + c : ℤ)) : ℚ) := by
        rw [← hprofile n]
        field_simp
      simp only [hF, Set.mem_setOf_eq]
      refine not_congr ?_
      rw [hCg, hprof, hmNc]
      constructor
      · intro h
        exact_mod_cast mul_left_cancel₀ hgQ h
      · intro h
        congr 1
        exact_mod_cast h
    have hFzero : ZeroLowerDensity F := by
      apply (zeroLowerDensity_iff_no_positive_lower_bound F).mpr
      intro dd hdd hFd
      have hE' := (lowerDensityAtLeast_iff_of_eventual_iff _ F N dd heq).mpr hFd
      exact (hzero'.not_positive_lower_bound dd hdd) hE'
    have hvpos : ∀ n, N ≤ n → 0 < v n := by
      intro n hn
      obtain ⟨-, -, h, -, -, -, -⟩ := htail n hn
      exact h
    have hnum : ∀ n, N ≤ n → u (n + 1) + v n = aN n * u n := by
      intro n hn
      obtain ⟨-, -, -, -, -, h, -⟩ := htail n hn
      exact h
    have hden : ∀ n, N ≤ n → v (n + 1) = aN n * v n := by
      intro n hn
      obtain ⟨-, -, -, -, -, -, h⟩ := htail n hn
      exact h
    have hcop : ∀ n, N ≤ n → Nat.Coprime (u n) (v n) := by
      intro n hn
      obtain ⟨-, -, -, h, -, -, -⟩ := htail n hn
      exact h
    obtain ⟨-, -, -, -, -, hirr⟩ :=
      primitive_zero_density_multiplier_irreducibility aN u v mN c N hmNpos hvpos hnum hden hcop
        hFzero
    haveI : Fact (Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) := ⟨hirr⟩
    have hrootα :
        (AdjoinRoot.root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) ^ 3
          = (AdjoinRoot.root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ))))
            - algebraMap ℚ (AdjoinRoot (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ))))
                (6 * (c : ℚ) / (mN : ℚ)) := by
      have hof : AdjoinRoot.of (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))
          = algebraMap ℚ (AdjoinRoot (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) :=
        RingHom.ext_rat _ _
      have h := AdjoinRoot.eval₂_root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))
      rw [hof, eval₂_cubicScalePolynomial] at h
      linear_combination h
    obtain ⟨β, hβmem, -, hβsq⟩ :=
      transport_square hss aN u v mN c N hmNpos hvpos hnum hden hcop hFzero
        (AdjoinRoot (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ))))
        (AdjoinRoot.root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) hrootα
    exact primitive_cubic_zero_density_impossible_of_square_specialisation
      aN u v mN c N hmNpos hvpos hnum hden hcop hFzero _ β hrootα hβmem hβsq
  constructor
  · have hcore' : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        ε * (X : ℝ) ≤ (exceptionCount E X : ℝ) := by
      by_contra h
      push_neg at h
      apply hcore
      intro ε hε N
      obtain ⟨X, hX1, hX2⟩ := h ε hε N
      exact ⟨X, hX1, hX2⟩
    obtain ⟨ε, hε, N, hN⟩ := hcore'
    refine ⟨ε, hε, N, ?_⟩
    intro X hX
    have h1 : ε * (((X + 1 : ℕ)) : ℝ) ≤ (exceptionCount E (X + 1) : ℝ) :=
      hN (X + 1) (by omega)
    have h2 : ε * (X : ℝ) ≤ ε * (((X + 1 : ℕ)) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      push_cast
      linarith
    linarith
  · rintro ⟨N, hN⟩
    apply hcore
    intro ε hε M
    have hbound : ∀ X : ℕ, exceptionCount E X ≤ N := by
      intro X
      have hsub : exceptionFinset E X ⊆ Finset.range N := by
        intro n hn
        simp only [exceptionFinset, Finset.mem_filter, Finset.mem_range] at hn ⊢
        by_contra hnN
        exact hn.2 (hN n (Nat.le_of_not_lt hnN))
      have h := Finset.card_le_card hsub
      simpa [exceptionCount] using h
    obtain ⟨X0, hX0⟩ := exists_nat_gt ((N : ℝ) / ε)
    refine ⟨max M X0, le_max_left _ _, ?_⟩
    have hle : (X0 : ℝ) ≤ ((max M X0 : ℕ) : ℝ) := by exact_mod_cast le_max_right M X0
    have hlt : (N : ℝ) / ε < ((max M X0 : ℕ) : ℝ) := lt_of_lt_of_le hX0 hle
    have hNlt : (N : ℝ) < ε * ((max M X0 : ℕ) : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hlt hε
      rw [div_mul_cancel₀ _ hε.ne'] at hmul
      linarith
    have hb : (exceptionCount E (max M X0) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hbound (max M X0)
    linarith
