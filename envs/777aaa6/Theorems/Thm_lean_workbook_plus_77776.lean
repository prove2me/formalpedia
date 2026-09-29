-- Prove2me | Theorems.Thm_lean_workbook_plus_77776
-- name    : lean_workbook_plus_77776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d4e92129-8f0a-4e06-98c9-f1ce27e6027c
-- statement:
--   Let $ a\ge b\ge c$ \n\n $ a^3 + b^3 + c^3 + 3abc - ( ab(a + b) + bc(b + c) + ca(c + a) + k(a^2 + b^2 + c^2 - ab - bc - ca) ) = (a + b - 2c)(a - b)^2 + \frac {1}{2} (c - k) ( ( a - b)^2 + (b - c)^2 + (c - a)^2)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77776 (a b c k : ℝ) (h₁ : a ≥ b ∧ b ≥ c) (h₂ : 0 ≤ k) : a^3 + b^3 + c^3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + k * (a^2 + b^2 + c^2 - a * b - b * c - c * a)) = (a + b - 2 * c) * (a - b)^2 + (1 / 2) * (c - k) * ((a - b)^2 + (b - c)^2 + (c - a)^2)   :=  by sorry
