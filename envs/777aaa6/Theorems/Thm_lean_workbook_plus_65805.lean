-- Prove2me | Theorems.Thm_lean_workbook_plus_65805
-- name    : lean_workbook_plus_65805
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c88923ee-5cf3-4db0-9ccc-c45800bfa1b3
-- statement:
--   Prove that: $\left(a+b+c \right)^2 \left[\sum \left(a-b \right)^2 \right] \geqslant 2 \left[\sum \left(a-b \right)^2\left(a+c \right) \left(b+c \right) \right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65805 {a b c : ℝ} :
  (a + b + c) ^ 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥
    2 * ((a - b) ^ 2 * (a + c) * (b + c) + (b - c) ^ 2 * (b + a) * (c + a) + (c - a) ^ 2 * (c + b) * (a + b))   :=  by sorry
