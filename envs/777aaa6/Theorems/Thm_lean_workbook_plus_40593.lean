-- Prove2me | Theorems.Thm_lean_workbook_plus_40593
-- name    : lean_workbook_plus_40593
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/db4d892a-be82-4975-a6df-6a059337050e
-- statement:
--   for $x,y,a,b>0$ one has $\dfrac {x^2} {a} + \dfrac {y^2} {b} \geq \dfrac {(x+y)^2} {a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40593 (x y a b : ℝ) (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b) : (x ^ 2 / a + y ^ 2 / b) ≥ (x + y) ^ 2 / (a + b)   :=  by sorry
