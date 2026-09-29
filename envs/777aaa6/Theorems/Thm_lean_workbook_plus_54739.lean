-- Prove2me | Theorems.Thm_lean_workbook_plus_54739
-- name    : lean_workbook_plus_54739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/7707d3c4-6018-4ba3-8aba-0e273992110e
-- statement:
--   Prove that $x=[x]+\{x\}$ where $[x]$ is the integer part and $\{x\}$ is the decimal part of $x.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54739 (x : ℝ) : x = Int.floor x + (x - Int.floor x)   :=  by sorry
