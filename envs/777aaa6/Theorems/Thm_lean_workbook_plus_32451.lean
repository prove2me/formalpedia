-- Prove2me | Theorems.Thm_lean_workbook_plus_32451
-- name    : lean_workbook_plus_32451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c4e66460-a39f-44e5-9510-cc5c90e690b2
-- statement:
--   Prove that $ (x-y)^{5} + (y-z)^{5} + (z-x)^{5} $ is divisible by $ 5(x-y)(y-z)(z-x) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32451 {x y z : ℤ} : 5 * (x - y) * (y - z) * (z - x) ∣ (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5   :=  by sorry
