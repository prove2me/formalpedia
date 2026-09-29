-- Prove2me | Theorems.Thm_lean_workbook_plus_76298
-- name    : lean_workbook_plus_76298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4c1b5d5f-65e9-4ec4-8d95-dde1ec1e2e8d
-- statement:
--   From $a+bc=b+ca=c+ab$ we take that $(a-b)(c-1)=0$ , $(b-c)(a-1)=0$ and $(c-a)(b-1)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76298 {a b c : ℝ} (h : a + b * c = b + c * a ∧ b + c * a = c + a * b) : (a - b) * (c - 1) = 0 ∧ (b - c) * (a - 1) = 0 ∧ (c - a) * (b - 1) = 0   :=  by sorry
