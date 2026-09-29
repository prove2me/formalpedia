-- Prove2me | Theorems.Thm_lean_workbook_plus_8773
-- name    : lean_workbook_plus_8773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4ad5f2c8-b708-4063-8842-af542618c1c9
-- statement:
--   Prove that $u^3-uv^2+v^3\ge 0$ for non-negative $u$ and $v$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8773 (u v : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) : u^3 - u * v^2 + v^3 ≥ 0   :=  by sorry
