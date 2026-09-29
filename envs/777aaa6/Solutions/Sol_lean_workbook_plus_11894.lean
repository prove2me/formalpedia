-- Prove2me | solution 1 for lean_workbook_plus_11894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:00.178893+00:00
-- url     : https://prove2.me/submissions/b410e207-16ee-49ba-93e9-30af4091b105

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n : ℝ, n ≠ 0 ∧ n + 5 ≠ 0 → 5 / (n * (n + 5)) = 1 / n - 1 / (n + 5) := by
  rintro n ⟨h₁,h₂⟩
  field_simp
  <;> ring
