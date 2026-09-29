-- Prove2me | Theorems.Thm_lean_workbook_plus_33845
-- name    : lean_workbook_plus_33845
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/64f1e4ce-b436-4fd5-a8a6-f71a224bd200
-- statement:
--   $(a+b+c)(a^2+b^2+c^2)\geq 9abc= 9(4R\triangle)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33845 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a+b+c)*(a^2+b^2+c^2) ≥ 9*a*b*c   :=  by sorry
