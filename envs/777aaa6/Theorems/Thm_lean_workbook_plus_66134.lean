-- Prove2me | Theorems.Thm_lean_workbook_plus_66134
-- name    : lean_workbook_plus_66134
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4dd9f7c5-9bf7-4e9a-8cd9-0a3411d6a7f8
-- statement:
--   Claim. Let $x$ and $y$ be positive integers such that $x\equiv y\pmod{3}$ , and $f$ a polynomial with integer coefficients. Then $f(x)\equiv f(y)\pmod{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66134 (x y : ℤ) (f : Polynomial ℤ) (h : x ≡ y [ZMOD 3]) : f.eval x ≡ f.eval y [ZMOD 3]   :=  by sorry
