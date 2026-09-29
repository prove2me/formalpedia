-- Prove2me | Theorems.Thm_lean_workbook_plus_50949
-- name    : lean_workbook_plus_50949
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3f15e180-6cbd-4be5-9a41-920e14cf0630
-- statement:
--   Show that $\frac{2}{\\pi}\\leqslant \\frac{\\sin x}{x}\\leqslant 1$ for $0\\leqslant x\\leqslant \\frac{\\pi}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50949 : ∀ x ∈ Set.Icc 0 (Real.pi / 2), 2 / Real.pi ≤ sin x / x ∧ sin x / x ≤ 1   :=  by sorry
