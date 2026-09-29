-- Prove2me | Theorems.Thm_lean_workbook_plus_24469
-- name    : lean_workbook_plus_24469
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/70b34559-7878-47ea-a1e3-6c4e8ec0b151
-- statement:
--   Prove that $(a^2-\sqrt{2}b)^2+(b^2-1)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24469 (a b : ℝ) : (a^2 - Real.sqrt 2 * b)^2 + (b^2 - 1)^2 ≥ 0   :=  by sorry
