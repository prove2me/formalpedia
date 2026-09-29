-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_zero_density_primitive_shape
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:39:33.259966+00:00
-- url     : https://prove2.me/submissions/611306d0-d979-42b7-9dce-00956c3f74a1

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_six_mul_risingBinomial
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_lowerDensityAtLeast_iff_of_eventual_iff
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_cubic_unit_constant_of_zero_lower_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_step_adjacent_coprime
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_primitive_integral_tail
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_zeroLowerDensity_iff_no_positive_lower_bound
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# The complete zero-lower-density primitive-shape reduction

The manuscript's primitive-shape lemma is stated
under zero lower density, not under the universal positive threshold. Its
unit-constant conclusion is proved here at exactly that hypothesis.
The arbitrary positive-threshold theorem must not reuse that conclusion.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR9











/-- A primitive tail identifies the full rational profile, not only the
agreement predicate at selected indices. -/
theorem binomial_profile_of_scaled_coefficients (κ η : ℚ) (g : ℕ) (m c : ℤ)
    (hg : 0 < g) (hm : (m : ℚ) * (g : ℚ) = 6 * κ)
    (hc : (c : ℚ) * (g : ℚ) = η) (n : ℕ) :
    (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) / (g : ℚ) =
      ((m * risingBinomial n + c : ℤ) : ℚ) := by
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  apply (div_eq_iff hgQ).mpr
  have hB : (6 : ℚ) * (risingBinomial n : ℚ) =
      (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
    exact_mod_cast six_mul_risingBinomial n
  push_cast
  linear_combination -(risingBinomial n : ℚ) * hm - hc - κ * hB
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : 0 < κ)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}) :
    ∃ (N g : ℕ) (m c : ℤ), 0 < g ∧ 0 < m ∧ (c = 1 ∨ c = -1) ∧
      (m : ℚ) * (g : ℚ) = 6 * κ ∧ (c : ℚ) * (g : ℚ) = η ∧
      (∀ n : ℕ, (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) / (g : ℚ) =
        ((m * risingBinomial n + c : ℤ) : ℚ)) ∧
      ∀ n, N ≤ n →
        Nat.gcd (C n) (D n) = g ∧
        0 < C n / g ∧ 0 < D n / g ∧
        Nat.Coprime (C n / g) (D n / g) ∧
        Nat.Coprime (C n / g) (C (n + 1) / g) ∧
        C (n + 1) / g + D n / g = a n * (C n / g) ∧
        D (n + 1) / g = a n * (D n / g) := by
  let E : Set ℕ := {n : ℕ | (C n : ℚ) ≠
    κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
  obtain ⟨N, g, m, c, hg, hm, hmcoeff, hccoeff, _hbez, htail⟩ :=
    rational_cubic_primitive_integral_tail a C D κ η hκ hCpos hDpos hC hD
      (hzero.not_positive_lower_bound (1 / 4) (by norm_num))
  let F : Set ℕ := {n : ℕ | ((C n / g : ℕ) : ℤ) ≠ m * risingBinomial n + c}
  have heq : ∀ n, N ≤ n → (n ∈ E ↔ n ∈ F) := by
    intro n hn
    obtain ⟨_hgcd, _hpC, _hpD, _hcop, _hnum, _hden, hagree⟩ := htail n hn
    exact not_congr hagree
  have hFzero : ZeroLowerDensity F := by
    apply (zeroLowerDensity_iff_no_positive_lower_bound F).mpr
    intro d hd hF
    have hE := (lowerDensityAtLeast_iff_of_eventual_iff E F N d heq).mpr hF
    exact (hzero.not_positive_lower_bound d hd) hE
  have hadj : ∀ n, N ≤ n → Nat.Coprime (C n / g) (C (n + 1) / g) := by
    intro n hn
    obtain ⟨_hgcd, _hpC, _hpD, hcop, hnum, _hden, _ha⟩ := htail n hn
    exact primitive_step_adjacent_coprime (a n) _ _ _ hnum hcop
  have hc := primitive_cubic_unit_constant_of_zero_lower_density
    (fun n ↦ C n / g) m c N hadj hFzero
  refine ⟨N, g, m, c, hg, hm, hc, hmcoeff, hccoeff,
    binomial_profile_of_scaled_coefficients κ η g m c hg hmcoeff hccoeff, ?_⟩
  intro n hn
  obtain ⟨hgcd, hpC, hpD, hcop, hnum, hden, _ha⟩ := htail n hn
  exact ⟨hgcd, hpC, hpD, hcop, hadj n hn, hnum, hden⟩
