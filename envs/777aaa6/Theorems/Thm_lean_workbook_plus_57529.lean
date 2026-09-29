-- Prove2me | Theorems.Thm_lean_workbook_plus_57529
-- name    : lean_workbook_plus_57529
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/07819bd2-b28a-431c-8661-87f4d0710003
-- statement:
--   In the eight-term sequence $A,B,C,D,E,F,G,H$ , the value of $C$ is 5 and the sum of any three consecutive terms is 30. What is $A+H$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57529 (A B C D E F G H : ℝ) (h₁ : C = 5) (h₂ : A + B + C = 30) (h₃ : B + C + D = 30) (h₄ : C + D + E = 30) (h₅ : D + E + F = 30) (h₆ : E + F + G = 30) (h₇ : F + G + H = 30) : A + H = 25   :=  by sorry
