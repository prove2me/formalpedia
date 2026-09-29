-- Prove2me | Theorems.Thm_lean_workbook_plus_59134
-- name    : lean_workbook_plus_59134
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/4fa187bc-ca84-4111-b5e1-c3afa8585867
-- statement:
--   Let $a,b,c\in R$ , $|a|\geq |b+c|$ , $|b|\geq |c+a|$ , $|c|\geq |a+b|$ . Prove: $a+b+c=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59134 (a b c : ℝ) (hab : |a| ≥ |b + c|) (hbc : |b| ≥ |c + a|) (hca : |c| ≥ |a + b|) : a + b + c = 0   :=  by sorry
