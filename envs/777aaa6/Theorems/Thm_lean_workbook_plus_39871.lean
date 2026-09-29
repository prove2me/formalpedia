-- Prove2me | Theorems.Thm_lean_workbook_plus_39871
-- name    : lean_workbook_plus_39871
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3c318791-208d-4f95-9c28-e8fadefb4a5d
-- statement:
--   Let $a,b,c > 0$ and $a + b + c \leq 1$ , prove that $\frac{1+a}{1-a}+\frac{1+b}{1-b}+\frac{1+c}{1-c}\leq \frac{3 + a + b + c}{3 - (a + b + c)} \cdot \left(\frac{b}{a}+\frac{c}{b}+\frac{a}{c}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39871 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a + b + c ≤ 1) :
  (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) ≤
    (3 + a + b + c) / (3 - (a + b + c)) * (b / a + c / b + a / c)   :=  by sorry
