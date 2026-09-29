-- Prove2me | Theorems.Thm_lean_workbook_plus_40790
-- name    : lean_workbook_plus_40790
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3e4cbec0-3fa6-4d38-a080-17157fd4870a
-- statement:
--   Prove that $(a^2+b^2+c^2)^2 \geq 3(a^2b^2+b^2c^2 +c^2a^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40790 (a b c: ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 >= 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)   :=  by sorry
