-- Prove2me | Theorems.Thm_lean_workbook_plus_30449
-- name    : lean_workbook_plus_30449
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d2763894-56be-4d29-8abf-4da729bb8af8
-- statement:
--   If $a,b,c>0$ ,prove $a/(a+2(b+c))+b/(b+2(c+a))+c/(c+2(a+b))$ ≥ $3/5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30449 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + 2 * (b + c)) + b / (b + 2 * (c + a)) + c / (c + 2 * (a + b))) ≥ 3 / 5   :=  by sorry
