-- Prove2me | Theorems.Thm_lean_workbook_plus_52041
-- name    : lean_workbook_plus_52041
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/96568217-5143-486d-9548-36a3e3fb9f22
-- statement:
--   Prove that \(\binom{n+2}{4}-\binom{n}{2}=2\binom{n}{3}+\binom{n}{4}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52041 (n : ℕ) : (n + 2).choose 4 - n.choose 2 = 2 * n.choose 3 + n.choose 4   :=  by sorry
