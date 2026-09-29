-- Prove2me | Theorems.Thm_lean_workbook_plus_38660
-- name    : lean_workbook_plus_38660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/63c9ef84-902a-4d52-b52b-6e2523b010ff
-- statement:
--   Indeed, $a+b+c=0\implies 0=a^3+b^3+c^3+3(-c)(-a)(-b)$ $\implies a^3+b^3+c^3=3abc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38660  (a b c : ℝ)
  (h₀ : a + b + c = 0) :
  a^3 + b^3 + c^3 = 3 * a * b * c   :=  by sorry
