-- Prove2me | Theorems.Thm_lean_workbook_plus_27813
-- name    : lean_workbook_plus_27813
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/51dca613-a2bf-49f5-902f-bebc18c57dca
-- statement:
--   Note that $a^2+b^2+c^2 \ge ab+bc+ca=1$ then $a^2+b^2 \ge 1-c^2, b^2+c^2\ge 1-a^2, c^2+a^2 \ge 1-b^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27813 (a b c: ℝ) (h : a * b + b * c + c * a = 1) :
  a * a + b * b ≥ 1 - c * c ∧ b * b + c * c ≥ 1 - a * a ∧ c * c + a * a ≥ 1 - b * b   :=  by sorry
