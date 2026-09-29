-- Prove2me | Theorems.Thm_lean_workbook_plus_40685
-- name    : lean_workbook_plus_40685
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cee66399-95cb-4afd-898f-9517d0e4aeba
-- statement:
--   Solve for $a$ in the system of equations: $\begin{cases}a=2-p\\9=2+p\end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40685 (a p : ℝ) (h₁ : a = 2 - p) (h₂ : 9 = 2 + p) : a = -5   :=  by sorry
