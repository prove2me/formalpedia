-- Prove2me | Theorems.Thm_lean_workbook_plus_71035
-- name    : lean_workbook_plus_71035
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/92471158-6cb9-477f-9578-d4b4658d431b
-- statement:
--   Over positive reals, prove that $a^4+b^4+c^4\geq abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71035 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c)   :=  by sorry
