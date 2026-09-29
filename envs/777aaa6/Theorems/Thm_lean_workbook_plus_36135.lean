-- Prove2me | Theorems.Thm_lean_workbook_plus_36135
-- name    : lean_workbook_plus_36135
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c7589a3f-0a8c-4362-b81a-f390033203e3
-- statement:
--   $\sum_{i=2}^{1007} \left(\frac{1}{2i}-\frac{1}{2i+1}\right) \le \frac{1}{6}-\frac{1}{4030} \le \frac{1}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36135 : ∑ i in (Finset.Icc 2 1007), (1 / (2 * i) - 1 / (2 * i + 1)) ≤ 1 / 6 - 1 / 4030 ∧ 1 / 6 - 1 / 4030 ≤ 1 / 6   :=  by sorry
