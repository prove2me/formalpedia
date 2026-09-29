-- Prove2me | Theorems.Thm_lean_workbook_plus_9793
-- name    : lean_workbook_plus_9793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8be0a16e-f2e1-4aab-ad28-2debcf270852
-- statement:
--   prove that, $\sqrt{(a^2+b^2)(c^2+d^2)}>= ac+bd$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9793 (a b c d : ℝ) : Real.sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) ≥ a * c + b * d   :=  by sorry
