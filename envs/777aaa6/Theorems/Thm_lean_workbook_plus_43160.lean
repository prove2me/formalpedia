-- Prove2me | Theorems.Thm_lean_workbook_plus_43160
-- name    : lean_workbook_plus_43160
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/98863b19-9fee-4fee-a064-af9baa104ca2
-- statement:
--   Prove that\nb) $ \frac {a^{2}}{b + c} + \frac {b^{2}}{c + a} + \frac {c^{2}}{a + b} + a + b + c\geq\frac {3}{2}\sqrt {3(a^{2} + b^{2} + c^{2})}$\n\nGood luck
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43160 : ∀ a b c : ℝ, (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) + a + b + c) ≥ (3 / 2) * Real.sqrt (3 * (a^2 + b^2 + c^2))   :=  by sorry
