-- Prove2me | Theorems.Thm_lean_workbook_plus_7128
-- name    : lean_workbook_plus_7128
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/17abcf05-cdbb-4d04-86e3-2e0a2d4b61f3
-- statement:
--   Hello, by the Hook-length formula, the answer is $\frac{9!}{\prod_{1\le i, j\le 3}\text{hook}(i,j)}=\frac{9!}{5\cdot 4\cdot 3\cdot 4 \cdot 3\cdot 2\cdot 3\cdot 2\cdot 1}=42.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7128 : 9! / (5 * 4 * 3 * 4 * 3 * 2 * 3 * 2 * 1) = 42   :=  by sorry
