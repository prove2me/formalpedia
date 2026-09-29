-- Prove2me | Theorems.Thm_lean_workbook_plus_2917
-- name    : lean_workbook_plus_2917
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/98ec6686-4191-4718-b49f-58bc21003a51
-- statement:
--   b) $0 \le \frac{t-1}{\ln(t)} \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2917 (t : ℝ) (ht : 1 < t) : 0 ≤ (t - 1) / Real.log t ∧ (t - 1) / Real.log t ≤ 1   :=  by sorry
