-- Prove2me | Theorems.Thm_lean_workbook_plus_17720
-- name    : lean_workbook_plus_17720
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c134f3f8-3058-4f09-b77e-7a02a14c1014
-- statement:
--   Given \( a = m^2 - n^2 \), \( b = 2mn \), and \( c = m^2 + n^2 \) where \( m \) and \( n \) are integers with no common factor, show that \( c = b + (m-n)^2 \) where \( (m-n)^2 \) is an odd square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17720 (a b c m n : ℤ) (h₁ : a = m^2 - n^2) (h₂ : b = 2*m*n) (h₃ : c = m^2 + n^2) (h₄ : Int.gcd m n = 1) : c = b + (m - n)^2   :=  by sorry
