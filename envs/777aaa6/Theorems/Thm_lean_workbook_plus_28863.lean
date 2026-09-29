-- Prove2me | Theorems.Thm_lean_workbook_plus_28863
-- name    : lean_workbook_plus_28863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/de41d2cc-840e-47aa-ab5c-4491ee37dbe7
-- statement:
--   Use Cauchy-Schwarz inequality to prove the inequality $(a^2+b^2+c^2)(b^2+c^2+a^2) \geq (ab+bc+ca)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28863 (a b c : ℝ) : (a^2+b^2+c^2)*(b^2+c^2+a^2) ≥ (a*b+b*c+c*a)^2   :=  by sorry
