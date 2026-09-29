-- Prove2me | Theorems.Thm_lean_workbook_plus_26623
-- name    : lean_workbook_plus_26623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/38bf6a61-0d4f-496e-93a5-f32efac47552
-- statement:
--   If $x$ is rational number, then $x = [x]+{x}$ , where $[x]$ is the integer part and ${x}$ is the fractional part.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26623 (x : ℚ) : x = ⌊x⌋ + (x - ⌊x⌋)   :=  by sorry
