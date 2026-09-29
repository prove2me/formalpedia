-- Prove2me | Theorems.Thm_lean_workbook_plus_11637
-- name    : lean_workbook_plus_11637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8d17da9e-6d62-4559-ba11-e54c784d4925
-- statement:
--   Show, for all positive integers $ n = 1,2, . . .,$ that 14 divides $ 3^{4n+2}+5^{2n+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11637 (n : ℕ) : 14 ∣ 3^(4*n+2) + 5^(2*n+1)   :=  by sorry
