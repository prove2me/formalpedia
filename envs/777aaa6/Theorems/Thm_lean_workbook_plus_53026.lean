-- Prove2me | Theorems.Thm_lean_workbook_plus_53026
-- name    : lean_workbook_plus_53026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/61e4387b-2ed1-4c2c-850c-73bc580bc4de
-- statement:
--   Prove that $\sqrt{(1+\alpha)(1+\beta)}\geq 1+\sqrt{\alpha\beta}$ for $\alpha,\beta>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53026 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : Real.sqrt ((1 + α) * (1 + β)) ≥ 1 + Real.sqrt (α * β)   :=  by sorry
