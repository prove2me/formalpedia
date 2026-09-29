-- Prove2me | Theorems.Thm_lean_workbook_plus_77210
-- name    : lean_workbook_plus_77210
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ec8118af-d473-42d0-9d3a-83c2dad1c354
-- statement:
--   Prove that $1+\sqrt{6}=\sqrt{1+6+2\sqrt{6}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77210 : 1 + Real.sqrt 6 = Real.sqrt (1 + 6 + 2 * Real.sqrt 6)   :=  by sorry
