-- Prove2me | Theorems.Thm_lean_workbook_plus_1519
-- name    : lean_workbook_plus_1519
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2fb90625-29b8-4c80-b6ad-bc1669cec470
-- statement:
--   Prove that $\lfloor x + n \rfloor = \lfloor x \rfloor + n$ where $n$ is an integer and $x$ is a real number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1519 (x : ℝ) (n : ℤ) : ⌊x + n⌋ = ⌊x⌋ + n   :=  by sorry
