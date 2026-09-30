-- Prove2me | solution 1 for lean_workbook_plus_4762
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:23:40.468544+00:00
-- url     : https://prove2.me/submissions/ea0af836-bd07-407b-81c2-3b229f3379b6

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ x:ℕ, 10^x ≡ 1 [ZMOD 3^2005] := by
  exact ⟨0, by rw [pow_zero]⟩
