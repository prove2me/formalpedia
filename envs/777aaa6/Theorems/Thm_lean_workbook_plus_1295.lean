-- Prove2me | Theorems.Thm_lean_workbook_plus_1295
-- name    : lean_workbook_plus_1295
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/22431b06-cda6-47e8-81d7-f2d22a717dba
-- statement:
--   Let $a,b,c\geq 0 $ and $a^2+b^2+c^2+2abc=1.$ Prove that\n\n $$(a+2b)^2 + (b+2c)^2 + (c+2a)^2 \leq 7$$\n $$(a+b)^2 + (b+c)(c+a) \leq \frac{5}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1295 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) :
  (a + 2 * b)^2 + (b + 2 * c)^2 + (c + 2 * a)^2 ≤ 7 ∧ (a + b)^2 + (b + c) * (c + a) ≤ 5 / 2   :=  by sorry
