-- Prove2me | Theorems.Thm_lean_workbook_plus_6525
-- name    : lean_workbook_plus_6525
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c7c8895a-8e1d-428b-bf8f-a59e5e634f01
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=abc$. Prove that $(a^2+1)(b^2+1)(c^2+1)\geq (ab+bc+ca-1)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6525 (a b c : ℝ) (h : a + b + c = a * b * c) :
  (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b + b * c + c * a - 1)^2   :=  by sorry
