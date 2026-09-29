-- Prove2me | solution 1 for lean_workbook_plus_21666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:57:32.65259+00:00
-- url     : https://prove2.me/submissions/c0d9a903-ef2f-450b-8eab-7634f8714428

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ∀ y : ℝ, y ∈ Set.Icc 0 1 →
    12 * y ^ 5 - 30 * y ^ 4 + 40 * y ^ 3 - 30 * y ^ 2 + 12 * y + 3 ≥ 3 := by
  rintro y ⟨hy0, hy1⟩
  have hp : (1 - y) ^ 6 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hq : 0 ≤ y ^ 6 := pow_nonneg hy0 _
  have he : 12 * y ^ 5 - 30 * y ^ 4 + 40 * y ^ 3 - 30 * y ^ 2 + 12 * y + 3 =
      5 + 2 * y ^ 6 - 2 * (1 - y) ^ 6 := by ring
  nlinarith only [hp, hq, he]
