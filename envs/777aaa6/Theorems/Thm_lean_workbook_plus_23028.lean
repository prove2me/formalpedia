-- Prove2me | Theorems.Thm_lean_workbook_plus_23028
-- name    : lean_workbook_plus_23028
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e42547eb-6903-45f6-98be-85c380299302
-- statement:
--   Prove that for any real numbers a and b, and any angle x, the following inequality holds: \\(asinx + bcosx \leq \sqrt{a^2 + b^2}\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23028 (a b x: ℝ) : a * Real.sin x + b * Real.cos x ≤ Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
