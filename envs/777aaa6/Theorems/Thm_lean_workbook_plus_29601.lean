-- Prove2me | Theorems.Thm_lean_workbook_plus_29601
-- name    : lean_workbook_plus_29601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/aacbe7c6-5ccc-44a7-b0ec-e51d88427afd
-- statement:
--   If $ 0<a\le b\le c$ show that : \n\n $ \frac{(a+b)(a+c)^2}{3}\ge 2abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29601 (a b c : ℝ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c) (h₂ : a ≤ b ∧ b ≤ c) :  (a + b) * (a + c) ^ 2 / 3 ≥ 2 * a * b * c   :=  by sorry
