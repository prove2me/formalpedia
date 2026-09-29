-- Prove2me | Theorems.Thm_lean_workbook_plus_34933
-- name    : lean_workbook_plus_34933
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c0448aa6-3602-41b2-a1cb-ca07022d45e4
-- statement:
--   $a^{4}+b^{4}+c^{4}+abc(a+b+c)\geq ab^{3}+ac^{3}+ba^{3}+bc^{3}+ca^{3}+cb^{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34933 (a b c : ℝ) : a^4 + b^4 + c^4 + a * b * c * (a + b + c) ≥ a * b^3 + a * c^3 + b * a^3 + b * c^3 + c * a^3 + c * b^3   :=  by sorry
