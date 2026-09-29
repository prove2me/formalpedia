-- Prove2me | Theorems.Thm_lean_workbook_plus_9328
-- name    : lean_workbook_plus_9328
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e24ef75c-a7aa-4d47-a742-16c9b5fc2844
-- statement:
--   Prove that for any integer $k$, $k^2$ is congruent to $0$, $1$, or $-1 \pmod{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9328 (k : ℤ) : (k ^ 2 ≡ 0 [ZMOD 3]) ∨ (k ^ 2 ≡ 1 [ZMOD 3]) ∨ (k ^ 2 ≡ -1 [ZMOD 3])   :=  by sorry
