-- Prove2me | Theorems.Thm_lean_workbook_plus_2300
-- name    : lean_workbook_plus_2300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/873d8f61-9b64-4d27-8aaa-479a1252379a
-- statement:
--   If $x$ is $20\%$ of $23$ and $y$ is $23\%$ of $20$ , compute $xy$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2300 (x y : ℝ) (hx : x = 20 / 100 * 23) (hy : y = 23 / 100 * 20) : x * y = 21.16   :=  by sorry
