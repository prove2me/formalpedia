-- Prove2me | Theorems.Thm_lean_workbook_plus_528
-- name    : lean_workbook_plus_528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1172e7f6-c87f-4d80-b4c0-b336db29794a
-- statement:
--   Denotes the fractional part, or $\{x\}=x-\lfloor x\rfloor$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_528 (x : ℝ) : (Int.fract x) = x - Int.floor x   :=  by sorry
