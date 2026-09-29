-- Prove2me | Theorems.Thm_lean_workbook_plus_68985
-- name    : lean_workbook_plus_68985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0406be34-9933-478e-a1b3-059614a25924
-- statement:
--   For $a;b;c;d \geq 0$ and satisfying $a^{2}+b^{2}+(a-b)^{2}=c^{2}+d^{2}+(c-d)^{2}$\nProve that: $a^{4}+b^{4}+(a-b)^{4}=c^{4}+d^{4}+(c-d)^{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68985 (a b c d : ℝ) (hab : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0)(habc : a^2 + b^2 + (a - b)^2 = c^2 + d^2 + (c - d)^2) : a^4 + b^4 + (a - b)^4 = c^4 + d^4 + (c - d)^4   :=  by sorry
