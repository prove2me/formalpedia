-- Prove2me | Theorems.Thm_lean_workbook_plus_53488
-- name    : lean_workbook_plus_53488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/470b5ad4-e7a2-4bf7-9ec4-9f44fea3b6ed
-- statement:
--   Verify that $2^6 \equiv 1 \pmod 7$, $4^3 \equiv 1 \pmod 9$, $6^{10} \equiv 1 \pmod{11}$, and $8^{12} \equiv 1 \pmod{13}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53488 :
  2^6 ≡ 1 [ZMOD 7] ∧ 4^3 ≡ 1 [ZMOD 9] ∧ 6^10 ≡ 1 [ZMOD 11] ∧ 8^12 ≡ 1 [ZMOD 13]   :=  by sorry
