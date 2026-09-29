-- Prove2me | Theorems.Thm_lean_workbook_plus_51582
-- name    : lean_workbook_plus_51582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7a8812ed-3f7b-4e60-8c57-711038bd9170
-- statement:
--   it is just AM-GM \n $a^4 + a^4 + a^4 + b^4 \geq 4\sqrt[4]{a^{12}b^4} = 4a^3b $ \n $b^4 + b^4 + b^4 + c^4 \geq 4\sqrt[4]{b^{12}c^4} = 4b^3c $ \n $c^4 + c^4 + c^4 + a^4 \geq 4\sqrt[4]{c^{12}a^4} = 4c^3a $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51582  (a b c : ℝ) :
  a^4 + a^4 + a^4 + b^4 ≥ 4 * (a^3 * b) ∧
  b^4 + b^4 + b^4 + c^4 ≥ 4 * (b^3 * c) ∧
  c^4 + c^4 + c^4 + a^4 ≥ 4 * (c^3 * a)   :=  by sorry
