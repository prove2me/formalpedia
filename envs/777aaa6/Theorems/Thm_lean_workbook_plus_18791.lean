-- Prove2me | Theorems.Thm_lean_workbook_plus_18791
-- name    : lean_workbook_plus_18791
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e1cbe7a6-744e-4c90-a228-beccdfbfd04b
-- statement:
--   $17^{2n+1}\equiv (-8)^{2n+1}\pmod{25} ...(3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18791 : ∀ n : ℕ, 17^(2 * n + 1) ≡ (-8)^(2 * n + 1) [ZMOD 25]   :=  by sorry
