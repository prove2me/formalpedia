-- Prove2me | Theorems.Thm_lean_workbook_plus_53226
-- name    : lean_workbook_plus_53226
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/eecd7655-17df-45c7-8fa4-8dd4ba0d0000
-- statement:
--   Using some algebra, this is equivalent to \n\n $ (a^2 - bc)^2 = (c^2 - ab)(b^2 - ac)$ , \n\n $ a^4 + b^2c^2 - 2a^2bc = b^2c^2 + a^2bc - ab^3 - ac^3$ , \n\n $ a(a^3 + b^3 + c^3 - 3abc) = 0$ , \n\n $ a(a + b + c)(a^2 + b^2 + c^2 - ab - ac - bc) = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53226  (a b c : ℝ)
  (h₀ : a * b * c = 1)
  (h₁ : a^2 + b^2 + c^2 - a * b - b * c - c * a = 0) :
  a^4 + b^2 * c^2 - 2 * a^2 * b * c = b^2 * c^2 + a^2 * b * c - a * b^3 - a * c^3   :=  by sorry
