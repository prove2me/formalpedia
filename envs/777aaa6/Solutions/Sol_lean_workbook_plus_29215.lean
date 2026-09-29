-- Prove2me | solution 1 for lean_workbook_plus_29215
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:31:58.468773+00:00
-- url     : https://prove2.me/submissions/85460f4e-0d7e-4deb-bffc-6b676fce4379

import Theorems.Thm_lean_workbook_plus_29215
import Mathlib.Tactic.Linarith

theorem solution : ∀ a b : ℝ, a^2 ≥ 0 → a^2 + b^2 ≥ 2 * a * b := by
  intro a b _; nlinarith [sq_nonneg (a - b)]
