-- Prove2me | Theorems.Thm_lean_workbook_plus_22065
-- name    : lean_workbook_plus_22065
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/85a8f864-2ad7-4ff6-84f8-8fe8d79b599e
-- statement:
--   For any real number $0 \le x \le 4$ , $$\sqrt{x} \ge \frac{x}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22065 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 4) : Real.sqrt x ≥ x / 2   :=  by sorry
