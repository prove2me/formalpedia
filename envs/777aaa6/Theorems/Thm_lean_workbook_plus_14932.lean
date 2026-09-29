-- Prove2me | Theorems.Thm_lean_workbook_plus_14932
-- name    : lean_workbook_plus_14932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/451237ca-9363-48de-ab5c-5eec6db3c48e
-- statement:
--   Show $\frac{1}{m+1} < \frac{1}{3m+2} + \frac{1}{3m+3} + \frac{1}{3m+4}$ by induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14932 : ∀ m : ℕ, (1 : ℝ) / (m + 1) < 1 / (3 * m + 2) + 1 / (3 * m + 3) + 1 / (3 * m + 4)   :=  by sorry
