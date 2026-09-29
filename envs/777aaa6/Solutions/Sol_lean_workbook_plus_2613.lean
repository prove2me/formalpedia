-- Prove2me | solution 1 for lean_workbook_plus_2613
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:54.948859+00:00
-- url     : https://prove2.me/submissions/f40f8e18-4d73-4add-8399-37970aa5fb8d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℕ → ℝ) (x0 : ℝ) (h : ∀ n, x n = x0) : ∃ l, ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε := by
  refine ⟨x0,?_⟩
  intro ε hε
  refine ⟨0,?_⟩
  intro n hn
  rw [h n,sub_self,abs_zero]
  exact hε
