-- Prove2me | Theorems.Thm_lean_workbook_plus_56339
-- name    : lean_workbook_plus_56339
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/951f0bbc-c1c0-4382-816f-69c91b2dab96
-- statement:
--   Let $a \ge 1$ and $b \ge 1$ . Show that $\log_a b = \frac{1}{\log_b a}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56339 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : Real.logb a b = 1 / Real.logb b a   :=  by sorry
