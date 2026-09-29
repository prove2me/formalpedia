-- Prove2me | Theorems.Thm_lean_workbook_plus_128
-- name    : lean_workbook_plus_128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/28ed8eee-ab27-4a52-99ea-dfd1b509688d
-- statement:
--   Prove that $ 6\cdot 4^n\equiv 6\pmod{9}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_128 : ∀ n:ℕ, 6 * 4 ^ n ≡ 6 [ZMOD 9]   :=  by sorry
