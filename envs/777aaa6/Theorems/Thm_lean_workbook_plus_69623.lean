-- Prove2me | Theorems.Thm_lean_workbook_plus_69623
-- name    : lean_workbook_plus_69623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/1be0409a-a03d-4bcb-b9d6-e8f52143fc61
-- statement:
--   Prove: $(3-c)^2+(3-b)^2+(3-a)^2 \geq 12$ -based on the fact that $a+b+c=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69623 (a b c : ℝ) (h : a + b + c = 3) : (3 - a) ^ 2 + (3 - b) ^ 2 + (3 - c) ^ 2 ≥ 12   :=  by sorry
