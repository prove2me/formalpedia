-- Prove2me | Theorems.Thm_lean_workbook_plus_75043
-- name    : lean_workbook_plus_75043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/74629bec-d647-49ab-8bd5-96a5fb67e275
-- statement:
--   Find the minimum value of $f(x,y)=\frac{2020x}{y}+\frac{y}{2020x}$ if $x,y$ are positive real numbers such that $x+y=2020$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75043 (x y : ℝ) (h₁ : 0 < x ∧ 0 < y) (h₂ : x + y = 2020) : 2 ≤ 2020 * x / y + y / (2020 * x)   :=  by sorry
