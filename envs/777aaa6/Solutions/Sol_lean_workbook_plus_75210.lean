-- Prove2me | solution 1 for lean_workbook_plus_75210
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:28.400278+00:00
-- url     : https://prove2.me/submissions/f63ae453-9c6b-462c-8eaa-8f29be5d27ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (n : ℤ) (h : n % 2 = 1) :
    ∃ k, n = 2 * k + 1 ∧ n^2 = 4 * k^2 + 4 * k + 1 := by
  have hn : n = 2 * (n / 2) + 1 := by omega
  refine ⟨n / 2, hn, ?_⟩
  conv_lhs => rw [hn]
  ring
