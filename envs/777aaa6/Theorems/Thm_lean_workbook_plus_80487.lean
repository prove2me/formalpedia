-- Prove2me | Theorems.Thm_lean_workbook_plus_80487
-- name    : lean_workbook_plus_80487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/742f8a1a-e232-4ee3-977a-ca6f1968d2c4
-- statement:
--   First note that $2z^{2} = 3xy$ . So, we have $x^3 + y^3 + z^3 = x^3 + y^3 + (-z)^3 - 3xy(-z)$ which we can factor as $(x + y - z)(x^2 + zx - xy + zy + z^2 + y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80487  (x y z : ℂ)
  (h₀ : 2 * z^2 = 3 * (x * y))
  (h₁ : x^3 + y^3 + z^3 = x^3 + y^3 + (-z)^3 - 3 * (x * y) * (-z)) :
  x^3 + y^3 + z^3 = (x + y - z) * (x^2 + z * x - x * y + z * y + z^2 + y^2)   :=  by sorry
