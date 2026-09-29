-- Prove2me | Theorems.Thm_lean_workbook_plus_51982
-- name    : lean_workbook_plus_51982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4c3c568b-b253-49d5-8a20-9ca3f988c7fe
-- statement:
--   Prove that $ \frac{a^2}{a^2+4}+\frac{2}{1+(a+1)^2} \geq \frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51982 (a : ℝ) : (a^2/(a^2 + 4) + 2/(1 + (a + 1)^2)) ≥ 3/5   :=  by sorry
