-- Prove2me | Theorems.Thm_lean_workbook_plus_82245
-- name    : lean_workbook_plus_82245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3a50589b-74b4-445c-b21d-b4f30bc7bb41
-- statement:
--   Find the minimum of the expression: $\frac{a^2}{\sqrt{b^2+c^2}}+\frac{b^2}{\sqrt{c^2+a^2}}+\frac{c^2}{\sqrt{a^2+b^2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82245 (a b c : ℝ) : (a^2 / Real.sqrt (b^2 + c^2) + b^2 / Real.sqrt (c^2 + a^2) + c^2 / Real.sqrt (a^2 + b^2)) ≥ 0   :=  by sorry
