-- Prove2me | Theorems.Thm_lean_workbook_plus_10151
-- name    : lean_workbook_plus_10151
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/43583c5b-5c44-4461-8426-0bd73a54aeda
-- statement:
--   Let $a, b, c$ are three real numbers, such that $a+b+c=0$ and $a^3+b^3+c^3=0$. Prove that $abc=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10151 (a b c : ℝ) (h1 : a + b + c = 0) (h2 : a^3 + b^3 + c^3 = 0) : a * b * c = 0   :=  by sorry
