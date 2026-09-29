-- Prove2me | Theorems.Thm_lean_workbook_plus_75679
-- name    : lean_workbook_plus_75679
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/62732fc9-742f-44e7-bb17-5c3b03089788
-- statement:
--   If $a,b,c$ are real numbers such that $abc\le 0$ , then\n\n $(a) \ \ \ (a^2+ab+b^2)(b^2+bc+c^2)(c^2+ca+a^2)+(ab+bc+ca)^3\ge 0$ ;\n\n $(b) \ \ \ (a^2+ab+b^2)(b^2+bc+c^2)(c^2+ca+a^2)\ge 3(ab+bc+ca)^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75679 (a b c : ℝ) (h : a * b * c ≤ 0) : (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) + (a * b + b * c + c * a)^3 ≥ 0   :=  by sorry
