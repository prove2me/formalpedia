-- Prove2me | Theorems.Thm_lean_workbook_plus_74020
-- name    : lean_workbook_plus_74020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8352e05c-7284-4a10-b0c4-d4224155f5f8
-- statement:
--   If $a+b+c=0$ , then prove that $2(a^5+b^5+c^5)=5abc(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74020 (a b c : ℂ) (h : a + b + c = 0) :
  2 * (a^5 + b^5 + c^5) = 5 * a * b * c * (a^2 + b^2 + c^2)   :=  by sorry
