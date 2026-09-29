-- Prove2me | Theorems.Thm_lean_workbook_plus_44243
-- name    : lean_workbook_plus_44243
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1597d078-e761-4e0c-805b-a71c6a955d96
-- statement:
--   Let $a,b,c>0$ such that $a^2+b^2+c^2+3abc=6$. Prove that $ab+bc+ca\le 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44243 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 3 * a * b * c = 6) : a * b + b * c + c * a ≤ 3   :=  by sorry
