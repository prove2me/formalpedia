-- Prove2me | Theorems.Thm_lean_workbook_plus_7558
-- name    : lean_workbook_plus_7558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f7514fd5-b608-451f-9c1d-f57cb0241bbc
-- statement:
--   Prove that if $2n \equiv 0 \pmod{3}$, then $n \equiv 0 \pmod{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7558 (n : ℤ) : 2 * n ≡ 0 [ZMOD 3] → n ≡ 0 [ZMOD 3]   :=  by sorry
