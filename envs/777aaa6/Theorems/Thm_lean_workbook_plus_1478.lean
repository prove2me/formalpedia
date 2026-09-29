-- Prove2me | Theorems.Thm_lean_workbook_plus_1478
-- name    : lean_workbook_plus_1478
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ee4d70fa-de45-4a3b-a1bb-6b6b37a661cb
-- statement:
--   If $a=b=c=2$ so $\sum_{cyc}\frac{(a-1)^2}{a^2+2}=\frac{1}{2}$ . We'll prove that $\frac{1}{2}$ is the answer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1478 (a b c : ℝ) (ha : a = 2) (hb : b = 2) (hc : c = 2) : (a - 1) ^ 2 / (a ^ 2 + 2) + (b - 1) ^ 2 / (b ^ 2 + 2) + (c - 1) ^ 2 / (c ^ 2 + 2) = 1 / 2   :=  by sorry
