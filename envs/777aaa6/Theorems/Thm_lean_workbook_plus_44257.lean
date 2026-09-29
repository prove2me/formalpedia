-- Prove2me | Theorems.Thm_lean_workbook_plus_44257
-- name    : lean_workbook_plus_44257
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/12db0f8b-2595-4567-9678-6a5e9a972803
-- statement:
--   Prove the given statement about the remainder of $a_n$ when divided by 4: $a_1\equiv 1; a_2\equiv 1; a_3\equiv 2; \text{for }n\geqslant 4 \text{ even, } a_n\equiv 1\pmod 4; \text{for }n\geqslant 5 \text{ odd, } a_n\equiv 0\pmod 4.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44257 (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 1) (a3 : a 2 = 2) (a_rec : ∀ n, a (n + 3) = a (n + 1) + a n) : ∀ n, (n ≥ 4 ∧ Even n → a n ≡ 1 [ZMOD 4]) ∧ (n ≥ 5 ∧ Odd n → a n ≡ 0 [ZMOD 4])   :=  by sorry
