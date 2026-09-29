-- Prove2me | Theorems.Thm_lean_workbook_plus_61308
-- name    : lean_workbook_plus_61308
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/09f29cac-aa86-45fe-bf6c-12e6f828ab88
-- statement:
--   $2.sin \alpha .cos \beta = sin( \alpha + \beta ) + sin( \alpha - \beta )$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61308 : 2 * Real.sin α * Real.cos β = Real.sin (α + β) + Real.sin (α - β)   :=  by sorry
