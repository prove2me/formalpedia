-- Prove2me | Theorems.Thm_lean_workbook_plus_21988
-- name    : lean_workbook_plus_21988
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f51b5bc5-5b34-4fd7-9940-574795e821b9
-- statement:
--   The correct interval is $x \in (-\infty, 2] $ U $\left(\frac{11}4, 4 \right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21988 (∀ x, (x <= 2 ∨ 11/4 < x ∧ x <= 4))   :=  by sorry
