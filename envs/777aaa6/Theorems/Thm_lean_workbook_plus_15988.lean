-- Prove2me | Theorems.Thm_lean_workbook_plus_15988
-- name    : lean_workbook_plus_15988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3760f690-b6a3-4647-ac6d-14462d294cb0
-- statement:
--   $2^{n-1}\equiv (-1)^{n-1}\pmod 3$ and so $2^{n}\equiv (-1)^{n-1}\times 2\pmod 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15988 (n : ℕ) : 2 ^ (n - 1) ≡ (-1) ^ (n - 1) [ZMOD 3]   :=  by sorry
