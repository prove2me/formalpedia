-- Prove2me | Theorems.Thm_lean_workbook_plus_66099
-- name    : lean_workbook_plus_66099
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/eb80e0b0-5ab0-4d01-b717-63b7f6a5d93d
-- statement:
--   in other words, the harmonic mean of $a$ and $b$ is $\frac{1}{\frac{\frac{1}{a}+\frac{1}{b}}{2}}$ simplified, it is $\frac{2ab}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66099 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 2 * a * b / (a + b) = 1 / ((1 / a + 1 / b) / 2)   :=  by sorry
