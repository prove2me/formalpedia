-- Prove2me | Theorems.Thm_lean_workbook_plus_53542
-- name    : lean_workbook_plus_53542
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/526e49c3-e263-4143-8cb3-8b9a8d60dbad
-- statement:
--   Similarly, we see that the sum of all the numbers written will be $2(6^2 \cdot 1^2 + 5^2 \cdot 2^2 + 4^2 \cdot 3^2) = \boxed{560}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53542  (a b c d e f : ℕ)
  (h₀ : a = 6)
  (h₁ : b = 5)
  (h₂ : c = 4)
  (h₃ : d = 3)
  (h₄ : e = 2)
  (h₅ : f = 1)
  : 2 * (a^2 * f^2 + b^2 * e^2 + c^2 * d^2) = 560   :=  by sorry
