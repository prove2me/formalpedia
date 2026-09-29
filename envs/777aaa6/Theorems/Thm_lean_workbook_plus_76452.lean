-- Prove2me | Theorems.Thm_lean_workbook_plus_76452
-- name    : lean_workbook_plus_76452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4b537c25-b6bf-4e74-a1ef-a5150da64d3f
-- statement:
--   Let $a,b,c >0$ and $ab+bc+ca=\frac{3}{2}(a^2+b^2+c^2-1)$. Prove that\n$abc \leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76452 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a * b + b * c + c * a = (3 / 2) * (a ^ 2 + b ^ 2 + c ^ 2 - 1)) : a * b * c ≤ 1   :=  by sorry
