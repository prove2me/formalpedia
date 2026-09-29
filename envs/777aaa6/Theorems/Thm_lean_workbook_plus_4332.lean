-- Prove2me | Theorems.Thm_lean_workbook_plus_4332
-- name    : lean_workbook_plus_4332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/96f71415-4c0e-4295-aecf-37a714759160
-- statement:
--   we have $ x+y=7$ and $ x^2 -y^2=21$ \n\nFactoring $ x^2 -y^2=21$ to get $ (x-y)(x+y)=21$ \n\nFrom there $ x-y=3$ . Now adding $ x+y=7$ to $ x-y=3$ yields $ x=5$ , $ y=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4332  (x y : ℝ)
  (h₀ : x + y = 7)
  (h₁ : x^2 - y^2 = 21) :
  x = 5 ∧ y = 2   :=  by sorry
