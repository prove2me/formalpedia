-- Prove2me | Theorems.Thm_lean_workbook_plus_65773
-- name    : lean_workbook_plus_65773
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f7afb159-2591-41dd-97d4-5ce6232918a0
-- statement:
--   Set $x=0$ , then $a \sin 0 + b \cos 0 = 0 \implies b = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65773 (a b : ℝ) (hx : x = 0) : a * Real.sin x + b * Real.cos x = 0 → b = 0   :=  by sorry
