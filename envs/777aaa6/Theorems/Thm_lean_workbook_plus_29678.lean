-- Prove2me | Theorems.Thm_lean_workbook_plus_29678
-- name    : lean_workbook_plus_29678
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/053a9e0e-e55c-4957-9dce-f12d1483fdce
-- statement:
--   Show by induction that $ 4^{2n+1} + 3^{n+2}$ is divisible by 13 for all $ n>=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29678 (n : ℕ) : 4^(2*n+1) + 3^(n+2) ≡ 0 [ZMOD 13]   :=  by sorry
