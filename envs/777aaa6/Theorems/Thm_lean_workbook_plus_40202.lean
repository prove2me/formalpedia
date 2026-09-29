-- Prove2me | Theorems.Thm_lean_workbook_plus_40202
-- name    : lean_workbook_plus_40202
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ac4ffcd7-8b3a-49ca-8f17-c60d6c1a499b
-- statement:
--   Adding $2xy$ to both sides of the given equation gives \n\n$x^2+2xy+y^2=z^2+2xy$ \n\nSince $x, y, z > 0$ , $z^2+2xy > z^2$ , so \n\n$x^2+2xy+y^2 > z^2$ \n\nTaking the positive square root of both sides gives \n\n$x+y>z$ \n\nand we're done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40202  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x^2 + y^2 = z^2) :
  x + y > z   :=  by sorry
