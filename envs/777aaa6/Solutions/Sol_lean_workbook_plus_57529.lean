-- Prove2me | solution 1 for lean_workbook_plus_57529
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:29.501213+00:00
-- url     : https://prove2.me/submissions/57b97425-7e18-4f1d-abf8-9c52f6178046

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B C D E F G H : ℝ) (h₁ : C = 5) (h₂ : A + B + C = 30) (h₃ : B + C + D = 30) (h₄ : C + D + E = 30) (h₅ : D + E + F = 30) (h₆ : E + F + G = 30) (h₇ : F + G + H = 30) : A + H = 25 := by
  (intros; linarith)
