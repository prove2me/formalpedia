-- Prove2me | Theorems.Thm_lean_workbook_plus_15029
-- name    : lean_workbook_plus_15029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9c00578b-4d25-4b34-85f8-b2f5dda84440
-- statement:
--   By Trivial Inequality, $(a-b)^2+(b-c)^2+(c-a)^2 \geq 0 \implies a^2+b^2+c^2 \geq ab+bc+ca$ , with equality when $a=b=c$ . (So basically your question is to find the equality case of the inequality $a^2+b^2+c^2 \geq ab+bc+ca$ .)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15029 (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 → a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
