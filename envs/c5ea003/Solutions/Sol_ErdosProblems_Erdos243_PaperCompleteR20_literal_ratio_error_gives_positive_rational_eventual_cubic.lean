-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_positive_rational_eventual_cubic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:29:59.902317+00:00
-- url     : https://prove2.me/submissions/d503d81c-7aa2-45bb-b34b-3836cc9ff100

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_leading_coefficient_pos_of_exact_eventual_cubic
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_literal_ratio_error_gives_exact_eventual_cubic
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: positivity of the rational cubic coefficient

The eventual cubic obtained from the literal ratio estimate has a nonnegative
leading coefficient because the original sequence is positive.  Vanishing of
that coefficient would make the sequence eventually constant, contradicting
the same literal ratio estimate at scale `n^3`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A D : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (D : ℝ) := by
  obtain ⟨K, B, N, hprofile⟩ :=
    literal_ratio_error_gives_exact_eventual_cubic C hpos hratio
  have hKpos := leading_coefficient_pos_of_exact_eventual_cubic
    C K B N hpos hprofile hratio
  let m : ℤ := iterIntForwardDiff 3 C N
  have hm : (m : ℝ) = 6 * K := by
    have h0 := hprofile N (le_rfl)
    have h1 := hprofile (N + 1) (by omega)
    have h2 := hprofile (N + 2) (by omega)
    have h3 := hprofile (N + 3) (by omega)
    dsimp [m]
    simp only [iterIntForwardDiff, intForwardDiff, Int.cast_sub]
    simp [risingCubic] at h0 h1 h2 h3
    push_cast
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  let A : ℚ := (m : ℚ) / 6
  have hA : (A : ℝ) = K := by
    dsimp [A]
    push_cast
    linarith
  let D : ℚ := (C N : ℚ) - A *
    (N : ℚ) * ((N : ℚ) + 1) * ((N : ℚ) + 2)
  have hD : (D : ℝ) = B := by
    have h0 := hprofile N (le_rfl)
    dsimp [D]
    push_cast
    rw [hA]
    simp [risingCubic] at h0 ⊢
    linarith
  refine ⟨A, D, ?_, N, ?_⟩
  · have hAposR : (0 : ℝ) < (A : ℝ) := hA.symm ▸ hKpos
    exact_mod_cast hAposR
  · intro n hn
    rw [hprofile n hn, hA, hD]
