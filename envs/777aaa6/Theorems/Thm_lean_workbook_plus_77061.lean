-- Prove2me | Theorems.Thm_lean_workbook_plus_77061
-- name    : lean_workbook_plus_77061
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/683725da-4076-4b3c-8a73-f87ac506b4ad
-- statement:
--   Prove that $\frac{1}{2} \cdot \frac{3}{4} \cdot \frac{5}{6} \cdot \frac{7}{8} \cdot \cdots \cdot \frac{47}{48} \cdot \frac{49}{50} < \frac{1}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77061 : (∏ i in Finset.Icc (1 : ℕ) 50, (i + 1) / (i + 2)) < 1 / 8   :=  by sorry
