-- Prove2me | Theorems.Thm_lean_workbook_plus_30931
-- name    : lean_workbook_plus_30931
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d58e0ccf-abd3-487f-905d-3f1c579c60a2
-- statement:
--   Prove that if $x>0$, then $g(x)=x+\frac{1}{x}\geq 2$ with equality if and only if $x=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30931 (x : ℝ) (hx: x > 0) : x + 1/x ≥ 2 ∧ (x = 1 ↔ x + 1/x = 2)   :=  by sorry
