-- Prove2me | Theorems.Thm_lean_workbook_plus_21364
-- name    : lean_workbook_plus_21364
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5d710393-8e87-42ac-9fe3-6915ec9baffb
-- statement:
--   Let $a,b,c >0$ and $a^2+b^2+c^2 +2abc=5.$ Prove that $ab+bc+ca\leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21364 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 5) : a * b + b * c + c * a ≤ 3   :=  by sorry
