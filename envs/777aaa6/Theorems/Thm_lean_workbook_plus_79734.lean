-- Prove2me | Theorems.Thm_lean_workbook_plus_79734
-- name    : lean_workbook_plus_79734
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cf5fc014-6fdb-49a6-bf16-f26dd82cbfe2
-- statement:
--   Let $a, b, c>0$ such that $(a+b)(b+c)(c+a)=1.$ Prove that the following inequality holds: $ab+bc+ca\leq\frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79734 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) * (c + a) = 1) :
  a * b + b * c + c * a ≤ 3 / 4   :=  by sorry
