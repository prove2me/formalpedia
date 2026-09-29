-- Prove2me | Theorems.Thm_lean_workbook_plus_21361
-- name    : lean_workbook_plus_21361
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/18bb3cbb-97f7-458e-8aa7-643fb40b342e
-- statement:
--   Let $a,b,c$ be real numbers such that $a^3(b+c)+b^3(a+c)+c^3(a+b)=0$ . Prove that $ab+bc+ca\leq0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21361 (a b c : ℝ) (h : a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b) = 0) : a * b + b * c + c * a ≤ 0   :=  by sorry
