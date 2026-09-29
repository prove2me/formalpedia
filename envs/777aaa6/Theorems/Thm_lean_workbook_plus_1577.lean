-- Prove2me | Theorems.Thm_lean_workbook_plus_1577
-- name    : lean_workbook_plus_1577
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c3a9b86a-74f5-48f5-bfcf-c781d019d895
-- statement:
--   Prove that $\frac{z}{z^2 + 1} \le \frac{1}{2}$ for $z \ge -\frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1577 (z : ℝ) (hz : -1/3 ≤ z) : z / (z^2 + 1) ≤ 1/2   :=  by sorry
