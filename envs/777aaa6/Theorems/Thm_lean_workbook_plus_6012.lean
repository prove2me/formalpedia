-- Prove2me | Theorems.Thm_lean_workbook_plus_6012
-- name    : lean_workbook_plus_6012
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f8b2c4fd-8f2d-42fe-a65b-0c60dc7a4785
-- statement:
--   $\frac{5!}{2!\cdot 3!}\cdot 2^{2}\cdot \frac{1}{64}= \frac{5}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6012 (h₁ : 5! = 120) (h₂ : 2! = 2) (h₃ : 3! = 6) (h₄ : 2^2 = 4) (h₅ : 64 = 2^6) : (5! / (2! * 3!)) * 2^2 * (1 / 64) = 5 / 8   :=  by sorry
