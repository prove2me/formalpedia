-- Prove2me | Theorems.Thm_lean_workbook_plus_50698
-- name    : lean_workbook_plus_50698
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f54d598c-6f2a-4627-9a48-708285a7d78e
-- statement:
--   Prove that $(ax+by)^2+(cx+dy)^2\leq(a^2+b^2+c^2+d^2)(x^2+y^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50698 (a b c d x y : ℝ) : (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2)   :=  by sorry
