-- Prove2me | Theorems.Thm_lean_workbook_plus_14027
-- name    : lean_workbook_plus_14027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8a5e2905-7f4e-473c-b987-c6f4325f08b5
-- statement:
--   Find term 4 of the sequence: $a_{n}=4 \cdot 3^{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14027 (a : ℕ → ℕ) (a_n : ∀ n, a n = 4 * 3 ^ (n - 1)) : a 4 = 108   :=  by sorry
