-- Prove2me | Theorems.Thm_lean_workbook_plus_66781
-- name    : lean_workbook_plus_66781
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/d06bc726-8af9-4748-838c-199e3e246627
-- statement:
--   if $ 0<a<b$ , prove that: $ a^3 - 3a - 2 \le b^3 - 3b + 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66781 (a b : ℝ) (h : a < b) (h1 : 0 < a) : a^3 - 3*a - 2 ≤ b^3 - 3*b + 2   :=  by sorry
