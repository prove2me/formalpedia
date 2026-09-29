-- Prove2me | Theorems.Thm_lean_workbook_plus_3174
-- name    : lean_workbook_plus_3174
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/012366d7-c868-4a6a-bf21-b9f053857fcb
-- statement:
--   Which can be prove with AM-GM $a^{2}+b^{2}\ge2ab$ $b^{2}+c^{2}\ge2bc$ $a^{2}+c^{2}\ge2ac$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3174 (a b c: ℝ) : a^2 + b^2 ≥ 2*a*b ∧ b^2 + c^2 ≥ 2*b*c ∧ a^2 + c^2 ≥ 2*a*c   :=  by sorry
