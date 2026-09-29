-- Prove2me | Theorems.Thm_lean_workbook_plus_57580
-- name    : lean_workbook_plus_57580
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/b173ba3a-4f42-481f-ab9c-d9637b563b3d
-- statement:
--   Manipulate the equation to get:\n\n$-a^3b^3c^3 + abc + a^3b^3c + a^3bc^3 + ab^3c^3 - abc^3 - ab^3c - a^3bc = -a(-1+a^2)b(-1+b^2)c(-1+c^2)$\n\nand\n\n$a^4b^2c^2 + b^4c^2a^2 + c^4a^2b^2 = abc(a^2 + b^2 + c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57580 ∀ a b c : ℤ, -a^3 * b^3 * c^3 + a * b * c + a^3 * b^3 * c + a^3 * b * c^3 + a * b^3 * c^3 - a * b * c^3 - a * b^3 * c - a^3 * b * c = -a * ( -1 + a^2) * b * ( -1 + b^2) * c * ( -1 + c^2) ∧ a^4 * b^2 * c^2 + b^4 * c^2 * a^2 + c^4 * a^2 * b^2 = a * b * c * (a^2 + b^2 + c^2)   :=  by sorry
