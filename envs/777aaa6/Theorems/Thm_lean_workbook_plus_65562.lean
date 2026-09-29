-- Prove2me | Theorems.Thm_lean_workbook_plus_65562
-- name    : lean_workbook_plus_65562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5846afba-bcd8-458f-9f2b-37371b30263a
-- statement:
--   $-1 = \frac{1}{-1}~~~~ \checkmark$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65562  (q e : ℚ)
  (h₀ : q = -1)
  (h₁ : e = 1 / -1) :
  q = e   :=  by sorry
