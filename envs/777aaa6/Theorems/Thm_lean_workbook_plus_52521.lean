-- Prove2me | Theorems.Thm_lean_workbook_plus_52521
-- name    : lean_workbook_plus_52521
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7651e117-f154-4f3c-8aa4-e23fa8bb0c22
-- statement:
--   Prove that if $ n\equiv 1,3 \mod 4$, then $ n^2 \equiv 1 \mod 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52521 {n : ℤ} (h : n ≡ 1 [ZMOD 4] ∨ n ≡ 3 [ZMOD 4]) : n ^ 2 ≡ 1 [ZMOD 4]   :=  by sorry
