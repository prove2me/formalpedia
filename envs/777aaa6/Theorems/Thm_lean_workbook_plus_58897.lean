-- Prove2me | Theorems.Thm_lean_workbook_plus_58897
-- name    : lean_workbook_plus_58897
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e564d432-7b6a-45e5-a497-e8defb43e900
-- statement:
--   Given the identity $a^2 - b^2 = (a + b)(a - b)$ and $a - b = 1$, show that $a^2 - b^2 = a + b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58897 (a b : ℝ) (h₁ : a - b = 1) : a^2 - b^2 = (a + b) * (a - b)   :=  by sorry
