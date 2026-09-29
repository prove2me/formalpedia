-- Prove2me | Theorems.Thm_lean_workbook_plus_80401
-- name    : lean_workbook_plus_80401
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/98ab3fe6-7f9f-49b0-963e-de987daa1ed5
-- statement:
--   x^3-13y^3=1453\\Rightarrow x^3\\equiv 10\\pmod{13}$ , impossible.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80401 : ∀ x y : ℤ, (x ^ 3 - 13 * y ^ 3 = 1453) → (x ^ 3 ≡ 10 [ZMOD 13])   :=  by sorry
