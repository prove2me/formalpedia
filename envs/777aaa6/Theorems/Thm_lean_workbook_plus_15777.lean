-- Prove2me | Theorems.Thm_lean_workbook_plus_15777
-- name    : lean_workbook_plus_15777
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4044e8c7-ad51-4758-be1f-e19176c57900
-- statement:
--   If $\ n\equiv 0\pmod{3}$ and $n=3x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15777 : ∀ n : ℕ, n ≡ 0 [ZMOD 3] → ∃ x : ℕ, n = 3 * x   :=  by sorry
