-- Prove2me | Theorems.Thm_lean_workbook_plus_44544
-- name    : lean_workbook_plus_44544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5269d4af-08ec-48d7-a5d9-ca1066618142
-- statement:
--   Find all $n$ such that $n\equiv1\mod6$ or $n\equiv5\mod6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44544 (n : ℕ) : n ≡ 1 [ZMOD 6] ∨ n ≡ 5 [ZMOD 6] ↔ n % 6 = 1 ∨ n % 6 = 5   :=  by sorry
