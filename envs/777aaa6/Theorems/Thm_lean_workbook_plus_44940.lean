-- Prove2me | Theorems.Thm_lean_workbook_plus_44940
-- name    : lean_workbook_plus_44940
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/4c4d9319-8c1a-4475-ba9d-cb9941904daf
-- statement:
--   Find the value of $ -1-(a-1)(b-1)(c-1)=ab+bc+ca-abc$ given $ a+b+c=3$ and $ a, b, c > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44940 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : -1 - (a - 1) * (b - 1) * (c - 1) = a * b + b * c + c * a - a * b * c   :=  by sorry
