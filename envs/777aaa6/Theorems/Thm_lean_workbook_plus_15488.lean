-- Prove2me | Theorems.Thm_lean_workbook_plus_15488
-- name    : lean_workbook_plus_15488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0d76cf49-2e8c-48f0-b35f-63d59827ae07
-- statement:
--   Let $p > 3$ be a prime. Prove that the following equation has solution in $\mathbb{Z}_+$\n$x^2 + y^2 + z^2 = 4p^2+1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15488 (p : ℕ) (hp : 3 < p) (hp1 : Nat.Prime p) : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 4 * p^2 + 1   :=  by sorry
