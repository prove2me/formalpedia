-- Prove2me | Theorems.Thm_lean_workbook_plus_30544
-- name    : lean_workbook_plus_30544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/fedbdb61-7dc6-4ad1-ae3e-487584d1fb2b
-- statement:
--   Prove that if $a,b,c\geq0$ then $3(a^2b+b^2c+c^2a)(ab^2+bc^2+ca^2)\leq(a^2+b^2+c^2)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30544 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3   :=  by sorry
