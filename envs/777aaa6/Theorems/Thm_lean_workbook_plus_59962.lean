-- Prove2me | Theorems.Thm_lean_workbook_plus_59962
-- name    : lean_workbook_plus_59962
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9c8509b3-30b4-43ec-874e-2e50059fcbfa
-- statement:
--   Let $a,$ $b,$ $c$ be positive real numbers such that $a^2+b^2+c^2=\frac{1}{3}.$ Prove that \n $\frac{1}{a^2-bc+1}+\frac{1}{b^2-ca+1}+\frac{1}{c^2-ab+1} \le 3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59962 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1 / 3) : 1 / (a^2 - b * c + 1) + 1 / (b^2 - c * a + 1) + 1 / (c^2 - a * b + 1) ≤ 3   :=  by sorry
