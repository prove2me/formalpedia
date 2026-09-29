-- Prove2me | Theorems.Thm_lean_workbook_plus_15720
-- name    : lean_workbook_plus_15720
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ca612998-ce53-4ff4-8664-6dad56c3950b
-- statement:
--   prove $(a+b)(b+c) \geq (\sqrt{bc}+\sqrt{ba})^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15720 : ∀ a b c : ℝ, (a+b)*(b+c) ≥ (Real.sqrt (b*c) + Real.sqrt (b*a))^2   :=  by sorry
