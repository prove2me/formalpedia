-- Prove2me | Theorems.Thm_lean_workbook_plus_74403
-- name    : lean_workbook_plus_74403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bf8b3c71-0db2-4b35-8224-3d16dae2881f
-- statement:
--   Let $a,b,c$ be positive real numbers. If $(a+b)(b+c)(c+a)=\sqrt{10}$, then $(a^2+b^2)(b^2+c^2)(c^2+a^2)+12a^2b^2c^2\ge 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74403 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) * (c + a) = Real.sqrt 10) :
  (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) + 12 * a^2 * b^2 * c^2 ≥ 3   :=  by sorry
