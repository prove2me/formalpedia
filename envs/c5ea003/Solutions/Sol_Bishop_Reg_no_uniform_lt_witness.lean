-- Prove2me | solution 1 for Bishop.Reg.no_uniform_lt_witness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:05:43.545984+00:00
-- url     : https://prove2.me/submissions/f6316491-ba59-42d2-bf66-4a0d2bfdbf02

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
open Bishop Bishop.Reg in
theorem solution (N : ℕ) :
    ∃ x y : Reg, Lt x y ∧ ∀ n ≤ N, ¬ (x.approx n + 2 / (n + 1 : ℚ) < y.approx n) := by
  -- the gap `2/(N+1)` is strictly positive but too small to be seen before stage `N+1`
  refine ⟨ofRat 0, ofRat (2 / ((N : ℚ) + 1)), ?_, ?_⟩
  · -- witnessed at `n = N + 1`
    refine ⟨N + 1, ?_⟩
    show (0 : ℚ) + 2 / (((N + 1 : ℕ) : ℚ) + 1) < 2 / ((N : ℚ) + 1)
    have h1 : (0 : ℚ) < (N : ℚ) + 1 := by positivity
    have h2 : (0 : ℚ) < ((N + 1 : ℕ) : ℚ) + 1 := by positivity
    rw [zero_add, div_lt_div_iff₀ h2 h1]
    push_cast
    linarith
  · -- but invisible at every stage `n ≤ N`
    intro n hn
    show ¬ ((0 : ℚ) + 2 / ((n : ℚ) + 1) < 2 / ((N : ℚ) + 1))
    have h1 : (0 : ℚ) < (N : ℚ) + 1 := by positivity
    have h2 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    have hle : (n : ℚ) ≤ (N : ℚ) := by exact_mod_cast hn
    rw [zero_add, not_lt, div_le_div_iff₀ h1 h2]
    linarith
