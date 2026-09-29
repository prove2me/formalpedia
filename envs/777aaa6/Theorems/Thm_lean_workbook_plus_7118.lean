-- Prove2me | Theorems.Thm_lean_workbook_plus_7118
-- name    : lean_workbook_plus_7118
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6acab9bf-1a68-4f13-91f9-a9533578ffe0
-- statement:
--   Prove that $2x\sqrt{x} - 3x + 1 \geq 0$ for $x > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7118 (x : ℝ) (hx : 0 < x) : 2 * x * Real.sqrt x - 3 * x + 1 ≥ 0   :=  by sorry
