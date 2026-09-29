-- Prove2me | Theorems.Thm_lean_workbook_plus_56740
-- name    : lean_workbook_plus_56740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/237d1dd6-4749-463f-8724-85bcc3ba35b6
-- statement:
--   $ \frac{5x-6-x^2}{2} \ge 0$ , so $ 2 \le x \le 3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56740 (x : ℝ) : (5*x-6-x^2)/2 ≥ 0 ↔ 2 ≤ x ∧ x ≤ 3   :=  by sorry
