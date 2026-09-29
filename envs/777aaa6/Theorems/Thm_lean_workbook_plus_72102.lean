-- Prove2me | Theorems.Thm_lean_workbook_plus_72102
-- name    : lean_workbook_plus_72102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3126c162-514b-47fa-ba04-2aca1759d9ef
-- statement:
--   If $a,b,c>0$ ,prove $a/(a+2(b+c))+b/(b+2(c+a))+c/(c+2(a+b))$ ≥ $3/5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72102 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (a + 2 * (b + c)) + b / (b + 2 * (c + a)) + c / (c + 2 * (a + b)) ≥ 3 / 5   :=  by sorry
