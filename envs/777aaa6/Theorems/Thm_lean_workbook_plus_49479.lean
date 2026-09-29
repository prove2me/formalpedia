-- Prove2me | Theorems.Thm_lean_workbook_plus_49479
-- name    : lean_workbook_plus_49479
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/339e3dc7-9e06-4578-b5c2-a31d457b7fed
-- statement:
--   Suppose two cubic polynomials $f(x)$ and $g(x)$ satisfy the following: $f(2)=g(4)$ ; $f(4)=g(8)$ ; $f(8)=g(16)$ ; $f(16)=g(32)+64$ . Find the value of $g(128)-f(64)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49479 (f g : ℝ → ℝ) (hf : ∀ x, f x = a₁ * x^3 + a₂ * x^2 + a₃ * x + a₄) (hg : ∀ x, g x = b₁ * x^3 + b₂ * x^2 + b₃ * x + b₄) (h₁ : f 2 = g 4) (h₂ : f 4 = g 8) (h₃ : f 8 = g 16) (h₄ : f 16 = g 32 + 64) : g 128 - f 64 = -9920   :=  by sorry
