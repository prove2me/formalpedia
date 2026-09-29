-- Prove2me | Theorems.Thm_lean_workbook_plus_31398
-- name    : lean_workbook_plus_31398
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d38a8d0b-1eb5-4201-ba94-05c120d87b2b
-- statement:
--   Prove that:\n$sin^{2}\dfrac{A}{2}+sin^{2}\dfrac{B}{2}+sin^{2}\dfrac{C}{2}\geq 4\left ( sin^{2}\dfrac{A}{2}.sin^{2}\dfrac{B}{2}+sin^{2}\dfrac{B}{2}.sin^{2}\dfrac{C}{2} +sin^{2}\dfrac{C}{2}.sin^{2}\dfrac{A}{2}\right )$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31398 : 
  ∀ A B C : ℝ, (sin (A / 2))^2 + (sin (B / 2))^2 + (sin (C / 2))^2 ≥ 
  4 * ((sin (A / 2))^2 * (sin (B / 2))^2 + (sin (B / 2))^2 * (sin (C / 2))^2 + (sin (C / 2))^2 * (sin (A / 2))^2)   :=  by sorry
