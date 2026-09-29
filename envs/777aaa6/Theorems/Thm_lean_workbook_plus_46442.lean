-- Prove2me | Theorems.Thm_lean_workbook_plus_46442
-- name    : lean_workbook_plus_46442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3e6c6a5f-abb1-4cd1-99b2-4b91d86817e9
-- statement:
--   Prove that $\frac{x}{x^2 + 1} \le \frac{1}{2}$ for $x \ge -\frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46442 (x : ℝ) (hx : x ≥ -1/3) : x / (x ^ 2 + 1) ≤ 1 / 2   :=  by sorry
