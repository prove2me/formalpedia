-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR21.transport_square
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:18:29.380879+00:00
-- url     : https://prove2.me/submissions/b86ea709-98cb-4d45-84f2-dda190dff6b7

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
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_zero_density_multiplier_irreducibility
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_natural_zero_lower_density_forces_modular_root_square
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





/-! ### `long243:res:transportsquare` -/
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
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀)
    (hroot : α ^ 3 = α - algebraMap ℚ L₀ (6 * (c : ℚ) / (m : ℚ))) :
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = α ^ 2 - 1 := by
  classical
  obtain ⟨hc, -, -, -, -, hirr⟩ :=
    primitive_zero_density_multiplier_irreducibility a u v m c T hm hv hnum hden hcop hzero
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hcQ : (c : ℚ) ≠ 0 := by
    rcases hc with rfl | rfl <;> norm_num
  set η : ℚ := 6 * (c : ℚ) / (m : ℚ) with hη
  have hη0 : η ≠ 0 := by
    rw [hη]
    exact div_ne_zero (by simpa using hcQ) hmQ
  set f : Polynomial ℚ := cubicScalePolynomial η with hf
  set H : Polynomial ℚ := Polynomial.X ^ 2 - 1 with hH
  have hfα : Polynomial.aeval α f = 0 := by
    rw [hf]
    simp only [cubicScalePolynomial, map_add, map_sub, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    rw [hroot]
    ring
  have hHα : Polynomial.aeval α H = α ^ 2 - 1 := by
    rw [hH]
    simp
  have hηL : algebraMap ℚ L₀ η ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap ℚ L₀).injective).mpr hη0
  have hHα0 : Polynomial.aeval α H ≠ 0 := by
    rw [hHα]
    intro h
    apply hηL
    have key : α * (α ^ 2 - 1) = -algebraMap ℚ L₀ η := by linear_combination hroot
    rw [h, mul_zero] at key
    exact neg_eq_zero.mp key.symm
  -- integral models
  set G : Polynomial ℤ :=
    Polynomial.C (m : ℤ) * Polynomial.X ^ 3 - Polynomial.C (m : ℤ) * Polynomial.X
      + Polynomial.C (6 * c) with hG
  set J : Polynomial ℤ := Polynomial.C ((m : ℤ) ^ 2) * (Polynomial.X ^ 2 - 1) with hJ
  have hGmap : G.map (Int.castRingHom ℚ) = Polynomial.C (m : ℚ) * f := by
    have hmapG : G.map (Int.castRingHom ℚ)
        = Polynomial.C (m : ℚ) * Polynomial.X ^ 3 - Polynomial.C (m : ℚ) * Polynomial.X
          + Polynomial.C (6 * (c : ℚ)) := by
      have h1 : (Int.castRingHom ℚ) ((m : ℤ)) = (m : ℚ) := by simp
      have h2 : (Int.castRingHom ℚ) (6 * c) = 6 * (c : ℚ) := by simp
      rw [hG]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
      rw [h1, h2]
    have hexp : Polynomial.C (m : ℚ) *
        (Polynomial.X ^ 3 - Polynomial.X + Polynomial.C η)
        = Polynomial.C (m : ℚ) * Polynomial.X ^ 3 - Polynomial.C (m : ℚ) * Polynomial.X
          + Polynomial.C ((m : ℚ) * η) := by
      rw [Polynomial.C_mul]
      ring
    have hcoef : (6 : ℚ) * (c : ℚ) = (m : ℚ) * η := by
      rw [hη]
      field_simp
    rw [hmapG, hf]
    simp only [cubicScalePolynomial]
    rw [hexp, hcoef]
  have hJmap : J.map (Int.castRingHom ℚ) = Polynomial.C ((m : ℚ) ^ 2) * H := by
    have h3 : (Int.castRingHom ℚ) ((m : ℤ) ^ 2) = (m : ℚ) ^ 2 := by simp
    rw [hJ, hH]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    rw [h3]
  -- the modular hypothesis
  have hmod : ∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
      (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
      (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
        IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r) := by
    refine ⟨max m 7, ?_⟩
    intro ℓ hℓ hℓN r hr
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓm : m < ℓ := lt_of_le_of_lt (le_max_left m 7) hℓN
    have hℓ7 : 7 < ℓ := lt_of_le_of_lt (le_max_right m 7) hℓN
    have hGval : (G.map (Int.castRingHom (ZMod ℓ))).eval r
        = (m : ZMod ℓ) * r ^ 3 - (m : ZMod ℓ) * r + ((6 * c : ℤ) : ZMod ℓ) := by
      rw [hG]
      simp
    have hJval : (J.map (Int.castRingHom (ZMod ℓ))).eval r
        = (m : ZMod ℓ) ^ 2 * (r ^ 2 - 1) := by
      rw [hJ]
      simp
    rw [hGval] at hr
    have hsix : ((6 : ℕ) : ZMod ℓ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 6]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have h6c : ((6 * c : ℤ) : ZMod ℓ) ≠ 0 := by
      rcases hc with rfl | rfl
      · intro h
        apply hsix
        push_cast at h ⊢
        linear_combination h
      · intro h
        apply hsix
        push_cast at h ⊢
        linear_combination -h
    have hmz : (m : ZMod ℓ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ m]
      intro hdvd
      have := Nat.le_of_dvd hm hdvd
      omega
    have h3z : (3 : ZMod ℓ) ≠ 0 := by
      have h : ((3 : ℕ) : ZMod ℓ) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 3]
        intro hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      simpa using h
    have hr0 : r ≠ 0 := by
      intro h
      apply h6c
      rw [h] at hr
      linear_combination hr
    have hrsq : r ^ 2 - 1 ≠ 0 := by
      intro h
      apply h6c
      have hcube : (m : ZMod ℓ) * r ^ 3 - (m : ZMod ℓ) * r = 0 := by
        linear_combination (m : ZMod ℓ) * r * h
      linear_combination hr - hcube
    have hfactor : 3 * (m : ZMod ℓ) * r ≠ 0 :=
      mul_ne_zero (mul_ne_zero h3z hmz) hr0
    have hroot' : (m : ZMod ℓ) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod ℓ) = 0 := by
      linear_combination hr
    have hsq := natural_zero_lower_density_forces_modular_root_square
      a u v m c T ℓ (by omega) hnum hden hzero r hroot' hfactor
    refine ⟨?_, ?_⟩
    · rw [hJval]
      exact mul_ne_zero (pow_ne_zero 2 hmz) hrsq
    · rw [hJval]
      obtain ⟨t, ht⟩ := hsq
      exact ⟨(m : ZMod ℓ) * t, by rw [ht]; ring⟩
  obtain ⟨β, hβmem, hβ0, hβsq⟩ :=
    hss L₀ α f H hirr hfα hHα0 m hm G J hGmap hJmap hmod
  exact ⟨β, hβmem, hβ0, by rw [hβsq, hHα]⟩
