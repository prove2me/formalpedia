-- Prove2me | Theorems.Thm_lean_workbook_plus_2544
-- name    : lean_workbook_plus_2544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f994f16e-3085-4467-ac46-f4e7da8fc1a7
-- statement:
--   Doesn't $\frac{6s^2}{2s^2\sqrt{3}}$ simplify to $\frac{3}{\sqrt{3}}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2544 (s : ℝ) (h : s ≠ 0) : 6 * s ^ 2 / (2 * s ^ 2 * Real.sqrt 3) = 3 / Real.sqrt 3   :=  by sorry
