-- Prove2me | Theorems.Thm_lean_workbook_plus_19642
-- name    : lean_workbook_plus_19642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/29eebdc6-9d36-4fc3-9ac6-049259e46ecd
-- statement:
--   $ \Longleftrightarrow(b-c)^2(-2b+a-2c)^2+(c-a)^2(-2c+b-2a)^2+(a-b)^2(-2a+c-2b)^2\geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19642 {a b c : ℝ} : (b - c) ^ 2 * (-2 * b + a - 2 * c) ^ 2 + (c - a) ^ 2 * (-2 * c + b - 2 * a) ^ 2 + (a - b) ^ 2 * (-2 * a + c - 2 * b) ^ 2 ≥ 0   :=  by sorry
