-- Prove2me | Theorems.Thm_lean_workbook_plus_54379
-- name    : lean_workbook_plus_54379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fb3188a9-75ec-432f-a3db-b42b758ea1e4
-- statement:
--   Let $a, b \ge 0$ and $a^3+b^3=2$ . Prove that: $a+b \le 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54379 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 3 + b ^ 3 = 2) : a + b ≤ 2   :=  by sorry
