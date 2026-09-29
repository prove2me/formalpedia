-- Prove2me | Theorems.Thm_lean_workbook_plus_7819
-- name    : lean_workbook_plus_7819
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/662252da-3e25-47a0-a2f7-832cb8d5a858
-- statement:
--   let $ x = \frac {b + c}{a}, y = \frac {c + a}{b}, z = \frac {a + b}{c}$\n\n$ x + y + z = 0 \implies bc(b + c) + ca(c + a) + ab(a + b) = 0$\n\n$ \implies (b + c)(c + a)(a + b) = 2abc \implies xyz = 2$\n\n$ \implies xy(x + y) = - 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7819  (x y z : ℝ)
  (h₀ : x + y + z = 0)
  (h₁ : x = (b + c) / a)
  (h₂ : y = (c + a) / b)
  (h₃ : z = (a + b) / c)
  (h₄ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₅ : a + b + c = 1) :
  x * y * z = 2 ∧ x * y * (x + y) = -2   :=  by sorry
