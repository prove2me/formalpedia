-- Prove2me | Theorems.Thm_lean_workbook_plus_8333
-- name    : lean_workbook_plus_8333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c998b763-af71-4f71-9008-05c1fde79ca8
-- statement:
--   If $(p, a) = 1$ and $(p, b) = 1$, and $p | a^2 + ab + b^2$, then prove that $p | 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8333 (p a b : ℕ) (h1 : (p, a) = 1 ∧ (p, b) = 1) (h2 : p ∣ a^2 + a*b + b^2) : p ∣ 3   :=  by sorry
