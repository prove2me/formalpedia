-- Prove2me | Theorems.Thm_lean_workbook_plus_81884
-- name    : lean_workbook_plus_81884
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b5492cec-c8cd-4e10-bdd3-d9f7092a2dfa
-- statement:
--   We multiply by $2$ on both sides: \n \n $$2a^2 + 2b^2 \geq (a+b)^2$$ \n $$2a^2 + 2b^2 \geq a^2 + 2ab + b^2$$ \n $$a^2 -2ab + b^2 \geq 0$$ \n $$(a-b)^2 \geq 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81884  (a b : ℝ) :
  2 * a^2 + 2 * b^2 ≥ (a + b)^2   :=  by sorry
