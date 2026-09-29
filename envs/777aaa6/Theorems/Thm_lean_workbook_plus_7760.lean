-- Prove2me | Theorems.Thm_lean_workbook_plus_7760
-- name    : lean_workbook_plus_7760
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7d525ff8-755e-466d-a48e-aa177e6eeae3
-- statement:
--   $(4a+4b+c)(\frac{a}{4}+\frac{b}{4}+c)\ge(a+b+c)^2\n $\frac{a}{4a+4b+c}\le\frac{a(a+b+4c)}{4(a+b+c)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7760 : ∀ a b c : ℝ, (4 * a + 4 * b + c) * (a / 4 + b / 4 + c) ≥ (a + b + c) ^ 2   :=  by sorry
