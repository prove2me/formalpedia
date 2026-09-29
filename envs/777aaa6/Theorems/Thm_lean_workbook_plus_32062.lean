-- Prove2me | Theorems.Thm_lean_workbook_plus_32062
-- name    : lean_workbook_plus_32062
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5eeca9e5-1f90-4e15-8ede-70d93d049928
-- statement:
--   Prove that: $\frac{\cos\alpha \sin\beta}{\sin\alpha}+\frac{\cos\beta \sin\gamma}{\sin\beta}+\frac{\cos\gamma \sin\alpha}{\sin\gamma}\ge\frac32$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32062 : ∀ α β γ : ℝ, (cos α * sin β / sin α + cos β * sin γ / sin β + cos γ * sin α / sin γ) ≥ 3 / 2   :=  by sorry
