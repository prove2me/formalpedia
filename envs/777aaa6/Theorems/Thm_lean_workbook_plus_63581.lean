-- Prove2me | Theorems.Thm_lean_workbook_plus_63581
-- name    : lean_workbook_plus_63581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/96f061ea-e9d6-46b9-8b5a-4af30317dc4c
-- statement:
--   If $a, b, c$ in a harmonic progression, then $1/a, 1/b, 1/c$ are in arithmetic progression. \n\nSubstitute $x = 1/a, y = 1/b, z = 1/c,$ where $x, y, z$ are in arithmetic progression. Then we also know that $2y = x + z.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63581  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 / a = x)
  (h₂ : 1 / b = y)
  (h₃ : 1 / c = z)
  (h₄ : a < b)
  (h₅ : b < c)
  (h₆ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₇ : x < y)
  (h₈ : y < z)
  (h₉ : 2 * y = x + z) :
  x + z = 2 * y   :=  by sorry
