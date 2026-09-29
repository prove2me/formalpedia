-- Prove2me | Theorems.Thm_lean_workbook_plus_19714
-- name    : lean_workbook_plus_19714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8822c75e-6df9-4a8e-90f9-8324ca337758
-- statement:
--   Prove $ab+bc+ac>0$ and $\frac{1}{ab}+\frac{1}{bc}+\frac{1}{ac}>0$ if $a, b, c$ have the same sign.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19714 (a b c : ℝ) (hab : a * b > 0) (hbc : b * c > 0) (hca : a * c > 0) : a * b + b * c + a * c > 0 ∧ 1 / (a * b) + 1 / (b * c) + 1 / (a * c) > 0   :=  by sorry
