-- Prove2me | solution 1 for lean_workbook_plus_24993
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:32:01.395491+00:00
-- url     : https://prove2.me/submissions/e2e24fb7-6814-47b9-9be2-fa27d6663225

import Theorems.Thm_lean_workbook_plus_24993
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) : a^2 - a * b + b^2 ≥ a * b := by
  nlinarith [sq_nonneg (a - b)]
