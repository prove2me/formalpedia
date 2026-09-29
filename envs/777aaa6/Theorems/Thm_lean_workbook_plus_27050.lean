-- Prove2me | Theorems.Thm_lean_workbook_plus_27050
-- name    : lean_workbook_plus_27050
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f7fa6fc2-121f-4840-86a4-197f2867859e
-- statement:
--   Prove \n $\frac{1}{6a^2+1}+\frac{1}{6b^2+1}+\frac{1}{6c^2+1}\geq \frac{9}{5}$ when $a+b+c=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27050 : ∀ a b c : ℝ, a + b + c = 1 → 1 / (6 * a ^ 2 + 1) + 1 / (6 * b ^ 2 + 1) + 1 / (6 * c ^ 2 + 1) ≥ 9 / 5   :=  by sorry
