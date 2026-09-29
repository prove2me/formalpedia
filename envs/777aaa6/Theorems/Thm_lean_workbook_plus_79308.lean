-- Prove2me | Theorems.Thm_lean_workbook_plus_79308
-- name    : lean_workbook_plus_79308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8961db43-607f-477f-873f-6e24c040d311
-- statement:
--   Solve the congruence $x^2\equiv 1 \pmod m$ using the equivalence to $(x-1)(x+1)\equiv 0 \pmod m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79308 (m : ℕ) (x : ℤ) : (x^2 ≡ 1 [ZMOD m]) ↔ ((x-1)*(x+1) ≡ 0 [ZMOD m])   :=  by sorry
