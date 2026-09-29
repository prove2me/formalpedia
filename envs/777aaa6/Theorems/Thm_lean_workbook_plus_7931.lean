-- Prove2me | Theorems.Thm_lean_workbook_plus_7931
-- name    : lean_workbook_plus_7931
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c87f0cb2-aa8b-44cf-9d18-c62d757fa42b
-- statement:
--   $x+y+z=2\Longrightarrow x+y=2-z$ . Denote $P=xy\ge0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7931 (x y z : ℝ) (h : x + y + z = 2) : xy ≥ 0   :=  by sorry
