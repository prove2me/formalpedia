-- Prove2me | Theorems.Thm_lean_workbook_plus_63703
-- name    : lean_workbook_plus_63703
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/34d74db1-3999-43ac-854c-8ff3c2e4b567
-- statement:
--   $ (\sum a)^{2} \leq 3(\sum a^{2})$ \nbecause $ 3(\sum a^{2}) - (\sum a)^{2} = \sum (a - b)^{2} \geq 0$ \nwhere all sums are cyclic
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63703 {a b c : ℝ} : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
