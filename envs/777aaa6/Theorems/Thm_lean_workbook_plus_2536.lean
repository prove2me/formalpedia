-- Prove2me | Theorems.Thm_lean_workbook_plus_2536
-- name    : lean_workbook_plus_2536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/aee0a93f-ed17-46b2-860d-04cbce37a241
-- statement:
--   Then\n\n$1 \le x \le 11 \Rightarrow 1 \le \lfloor x\rfloor \le 11$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2536 (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 11) : 1 ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ 11   :=  by sorry
