-- Prove2me | solution 1 for lean_workbook_plus_77752
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:49:22.980388+00:00
-- url     : https://prove2.me/submissions/d3766bba-c345-4348-a23a-a217ea65e9c7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n m : ℕ) (k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⌊(n:ℝ)^(1/k)⌋ = m) ↔ (m + 1 > (n:ℝ)^(1/k) ∧ (n:ℝ)^(1/k) ≥ m) := by
  have hfloor (x : ℝ) (j : ℕ) : (⌊x⌋ = (j : ℤ)) ↔ ((j : ℝ)+1 > x ∧ x ≥ (j : ℝ)) := by
    simpa only [Int.cast_natCast, and_comm] using (Int.floor_eq_iff : ⌊x⌋ = (j : ℤ) ↔ ((j : ℤ) : ℝ) ≤ x ∧ x < ((j : ℤ) : ℝ)+1)
  exact hfloor _ m
