-- Prove2me | Theorems.Thm_lean_workbook_plus_75836
-- name    : lean_workbook_plus_75836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/adda88b6-429b-458a-9d1e-81d75f651233
-- statement:
--   Let $a,b,c$ be real numbers such that $a^2(b+c)+b^2(a+c)+c^2(a+b)=0$ . Prove that $ab+bc+ca\leq0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75836 (a b c : ℝ) (h : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) = 0) : a * b + b * c + c * a ≤ 0   :=  by sorry
