-- Prove2me | Theorems.Thm_lean_workbook_plus_42055
-- name    : lean_workbook_plus_42055
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/242544de-3f54-4213-9ed6-8e583ccacc29
-- statement:
--   Let $a>b>c$ be real numbers. Prove that $a^{2}(b-c)+b^{2}(c-a)+c^{2}(a-b)>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42055 (a b c : ℝ) (hx: a > b ∧ b > c) : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) > 0   :=  by sorry
