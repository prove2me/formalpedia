-- Prove2me | Theorems.Thm_lean_workbook_plus_73693
-- name    : lean_workbook_plus_73693
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2b404ad0-4514-4dc2-ab31-a49a8744314f
-- statement:
--   Let $a,b,c$ be any real numbers. Prove that $(a+b+c)^2\ge3\bigl(\min(a,b)\max(b,c)+\min(b,c)\max(c,a)+\min(c,a)\max(a,b)\bigr).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73693 (a b c : ℝ) :
  (a + b + c) ^ 2 ≥ 3 * (min a b * max b c + min b c * max c a + min c a * max a b)   :=  by sorry
