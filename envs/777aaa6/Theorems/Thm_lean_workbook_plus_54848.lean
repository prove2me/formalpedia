-- Prove2me | Theorems.Thm_lean_workbook_plus_54848
-- name    : lean_workbook_plus_54848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/20db3ace-48d5-46b0-a5ad-24a0504af449
-- statement:
--   Prove that $a^4+b^4+c^4\geq abc(a+b+c)$ using the inequality $x^2+y^2+z^2\geq xy+yz+zx$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54848 {a b c : ℝ} : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c)   :=  by sorry
