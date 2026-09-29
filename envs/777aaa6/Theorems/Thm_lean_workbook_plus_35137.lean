-- Prove2me | Theorems.Thm_lean_workbook_plus_35137
-- name    : lean_workbook_plus_35137
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a207fcd0-1646-4399-8699-e3684afeb5c9
-- statement:
--   Rewrite $a \sin x + b \cos x$ as $\sqrt{a^2 + b^2} (\dfrac{a}{\sqrt{a^2 + b^2}} \sin x + \dfrac{b}{\sqrt{a^2 + b^2}} \cos x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35137 (a b : ℝ) : a * sin x + b * cos x = Real.sqrt (a ^ 2 + b ^ 2) * (a / Real.sqrt (a ^ 2 + b ^ 2) * sin x + b / Real.sqrt (a ^ 2 + b ^ 2) * cos x)   :=  by sorry
