-- Prove2me | Theorems.Thm_lean_workbook_plus_74788
-- name    : lean_workbook_plus_74788
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c3b4c956-54a2-493c-82e7-a3836342d56f
-- statement:
--   solLet $a=x$ and $b=y.$ Then, $a^2+2b^2=x^2+2y^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74788 (a b x y : ℤ) (h₁ : a = x) (h₂ : b = y) : a^2 + 2 * b^2 = x^2 + 2 * y^2   :=  by sorry
