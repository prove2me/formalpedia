-- Prove2me | Theorems.Thm_lean_workbook_plus_52395
-- name    : lean_workbook_plus_52395
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5340045f-d40c-4b3a-ae55-3c7e6cac36c2
-- statement:
--   Absolute value of a complex number represents (geometrically) its distance from the origin. So if $z=a + bi$ , then $|z| = \sqrt{a^2 + b^2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52395 (a b : ℝ) : Complex.abs (a + b * Complex.I) = Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
