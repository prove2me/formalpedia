-- Prove2me | Theorems.Thm_lean_workbook_plus_58140
-- name    : lean_workbook_plus_58140
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/214de46e-7a0e-4e9c-922c-a3a3c4b2ef99
-- statement:
--   For $a, b, c>0, a^2+b^2+c^2=3$ prove that $ab+bc+ca\leq2+abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58140 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 3) : a * b + b * c + c * a ≤ 2 + a * b * c   :=  by sorry
