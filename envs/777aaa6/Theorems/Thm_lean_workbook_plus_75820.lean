-- Prove2me | Theorems.Thm_lean_workbook_plus_75820
-- name    : lean_workbook_plus_75820
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e91446f9-7179-447e-b30a-2eecd7c93fcc
-- statement:
--   For $0<a,b,c,d<1$ . Prove that: $(1-a)(1-b)(1-c)(1-d)>1-a-b-c-d$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75820 (a b c d : ℝ) (hab : 0 < a ∧ a < 1) (hbc : 0 < b ∧ b < 1) (hcd : 0 < c ∧ c < 1) (hded : 0 < d ∧ d < 1) : (1 - a) * (1 - b) * (1 - c) * (1 - d) > 1 - a - b - c - d   :=  by sorry
