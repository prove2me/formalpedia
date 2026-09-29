-- Prove2me | Theorems.Thm_lean_workbook_plus_11680
-- name    : lean_workbook_plus_11680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/0f6cdf86-8891-4da0-974a-9ce9f8bc10d5
-- statement:
--   Let $a, b, c>0$ and $(a+b)(b+c)(c+a)=3(a+b+c-\frac{1}{3}).$ Prove that $abc\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11680 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) * (c + a) = 3 * (a + b + c - 1 / 3)) : a * b * c ≤ 1   :=  by sorry
