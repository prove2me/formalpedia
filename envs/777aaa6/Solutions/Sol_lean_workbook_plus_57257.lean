-- Prove2me | solution 1 for lean_workbook_plus_57257
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:11:14.966321+00:00
-- url     : https://prove2.me/submissions/a59cd1dd-f62f-4b0c-8dac-f4f0d2a16f3b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c : ℝ) : |a| + |b| + |c| + |a + b + c| ≥ |a + b| + |b + c| + |c + a| := by
  rcases abs_cases (a + b) with ⟨hab, _⟩ | ⟨hab, _⟩ <;>
    rcases abs_cases (b + c) with ⟨hbc, _⟩ | ⟨hbc, _⟩ <;>
    rcases abs_cases (c + a) with ⟨hca, _⟩ | ⟨hca, _⟩ <;>
    linarith only [hab, hbc, hca, le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b, le_abs_self c, neg_le_abs c, le_abs_self (a + b + c), neg_le_abs (a + b + c)]
