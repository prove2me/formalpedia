-- Prove2me | Theorems.Thm_lean_workbook_plus_73348
-- name    : lean_workbook_plus_73348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/59878ba1-6a02-4e3d-8351-de9c711823d7
-- statement:
--   Does there exist an integer $x$ satisfying the following conditions? $$10x\equiv 1(\text{mod} \ 21)$$ $$5x\equiv 2(\text{mod} \ 6)$$ $$4x\equiv 1(\text{mod} \ 7)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73348 (x : ℤ) : (10 * x ≡ 1 [ZMOD 21] ∧ 5 * x ≡ 2 [ZMOD 6] ∧ 4 * x ≡ 1 [ZMOD 7]) → x ≡ 19 [ZMOD 42]   :=  by sorry
