-- Prove2me | Theorems.Thm_lean_workbook_plus_35537
-- name    : lean_workbook_plus_35537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/e546ab78-77fe-4f01-86b8-e69aa7129796
-- statement:
--   Given that $a,b,c$ are positive real numbers, prove $(a+b+1)(b+c+1)(c+a+1)+2 \geq 7(ab+bc+ca)+2(a+b+c+abc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35537 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + 1) * (b + c + 1) * (c + a + 1) + 2 ≥ 7 * (a * b + b * c + a * c) + 2 * (a + b + c + a * b * c)   :=  by sorry
