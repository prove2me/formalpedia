-- Prove2me | Theorems.Thm_lean_workbook_plus_19328
-- name    : lean_workbook_plus_19328
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bf3fba26-6b42-4f7e-8545-a9e93a1abe6c
-- statement:
--   Prove that $ \frac{ax}{a+x}+\frac{by}{b+y} \leq \frac{(a+b)(x+y)}{a+b+x+y}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19328 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) : (a * x / (a + x) + b * y / (b + y)) ≤ (a + b) * (x + y) / (a + b + x + y)   :=  by sorry
