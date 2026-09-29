-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_eventually_constant
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:04:30.018129+00:00
-- url     : https://prove2.me/submissions/eb83b055-902d-4c2e-94c5-513e31a264ea

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterIntForwardDiff_cast
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_add
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_const_mul
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_tendsto_zero
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: exact eventual cubic profile

Once the integer third difference is constant, the residual's third
difference is constant as well.  Every positive-order difference of the
residual tends to zero, so descending through the differences makes the
residual itself eventually constant.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter

theorem third_difference_risingCubic (n : ℕ) :
    iterRealForwardDiff 3 risingCubic n = 6 := by
  simp [iterRealForwardDiff, realForwardDiff, risingCubic]
  ring

theorem eventually_zero_of_tendsto_zero_of_forwardDiff_eventually_zero
    (u : ℕ → ℝ)
    (hu : Tendsto u atTop (nhds 0))
    (hdiff : ∀ᶠ n in atTop, realForwardDiff u n = 0) :
    ∀ᶠ n in atTop, u n = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hdiff
  have hconst : ∀ n, N ≤ n → u n = u N := by
    intro n hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction d with
    | zero => simp
    | succ d ih =>
        have hz := hN (N + d) (by omega)
        simp only [realForwardDiff] at hz
        have hstep : u (N + d + 1) = u (N + d) := by linarith
        rw [show N + (d + 1) = N + d + 1 by omega, hstep, ih (by omega)]
  have hconstT : Tendsto (fun _ : ℕ => u N) atTop (nhds 0) := by
    apply hu.congr'
    exact eventually_atTop.2 ⟨N, fun n hn => hconst n hn⟩
  have huN : u N = 0 := tendsto_nhds_unique tendsto_const_nhds hconstT
  exact eventually_atTop.2 ⟨N, fun n hn => (hconst n hn).trans huN⟩
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ) (N : ℕ)
    (hdecomp : (fun n : ℕ => (C n : ℝ)) = fun n : ℕ => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0))
    (hthird : ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N) :
    ∃ N' : ℕ, ∀ n, N' ≤ n → r n = r N' := by
  let c : ℝ := (iterIntForwardDiff 3 C N : ℤ) - 6 * K
  have hthirdR : ∀ᶠ n in atTop, iterRealForwardDiff 3 r n = c := by
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hsplit : iterRealForwardDiff 3 (fun j => (C j : ℝ)) n =
        K * 6 + iterRealForwardDiff 3 r n := by
      rw [hdecomp, iterRealForwardDiff_add, iterRealForwardDiff_const_mul]
      simp only [third_difference_risingCubic]
    rw [← iterIntForwardDiff_cast] at hsplit
    rw [hthird n hn] at hsplit
    change iterRealForwardDiff 3 r n = (iterIntForwardDiff 3 C N : ℝ) - 6 * K
    linarith
  have hthirdZero : Tendsto (iterRealForwardDiff 3 r) atTop (nhds 0) := by
    simpa [iterRealForwardDiff] using iterRealForwardDiff_tendsto_zero hr 2
  have hcT : Tendsto (fun _ : ℕ => c) atTop (nhds 0) :=
    hthirdZero.congr' hthirdR
  have hc : c = 0 := tendsto_nhds_unique tendsto_const_nhds hcT
  have hz3 : ∀ᶠ n in atTop, iterRealForwardDiff 3 r n = 0 := by
    filter_upwards [hthirdR] with n hn
    exact hn.trans hc
  have hdiff2 : ∀ᶠ n in atTop,
      realForwardDiff (iterRealForwardDiff 2 r) n = 0 := by
    simpa [iterRealForwardDiff] using hz3
  have hlim2 : Tendsto (iterRealForwardDiff 2 r) atTop (nhds 0) := by
    simpa [iterRealForwardDiff] using iterRealForwardDiff_tendsto_zero hr 1
  have hz2 := eventually_zero_of_tendsto_zero_of_forwardDiff_eventually_zero
    (iterRealForwardDiff 2 r) hlim2 hdiff2
  have hdiff1 : ∀ᶠ n in atTop,
      realForwardDiff (realForwardDiff r) n = 0 := by
    simpa [iterRealForwardDiff] using hz2
  have hz1 := eventually_zero_of_tendsto_zero_of_forwardDiff_eventually_zero
    (realForwardDiff r) hr hdiff1
  obtain ⟨N', hN'⟩ := eventually_atTop.1 hz1
  refine ⟨N', ?_⟩
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => simp
  | succ d ih =>
      have hz := hN' (N' + d) (by omega)
      simp only [realForwardDiff] at hz
      have hstep : r (N' + d + 1) = r (N' + d) := by linarith
      rw [show N' + (d + 1) = N' + d + 1 by omega, hstep, ih (by omega)]
