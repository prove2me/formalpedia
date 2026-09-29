-- Prove2me | Theorems.Thm_lean_workbook_plus_48988
-- name    : lean_workbook_plus_48988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/2ea26f83-9ef6-4bf7-ac35-27c686bd0cfb
-- statement:
--   For any $a \epsilon Z$, ${ a }^{ 2 }(mod\quad 4)\equiv 0,1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48988 (a : ℤ) : a^2 ≡ 0 [ZMOD 4] ∨ a^2 ≡ 1 [ZMOD 4]   :=  by sorry
