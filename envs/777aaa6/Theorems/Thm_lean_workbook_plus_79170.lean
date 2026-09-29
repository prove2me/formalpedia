-- Prove2me | Theorems.Thm_lean_workbook_plus_79170
-- name    : lean_workbook_plus_79170
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/9b7517c4-b948-45b9-9aaf-79d36e1dfa65
-- statement:
--   Prove that for non-negative a, b, c\n\n1.\n $ \frac{a+\sqrt{ab}}{2} \leq \sqrt{a \times \frac{a+b}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79170 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  (a + Real.sqrt (a * b)) / 2 ≤ Real.sqrt (a * (a + b) / 2)   :=  by sorry
