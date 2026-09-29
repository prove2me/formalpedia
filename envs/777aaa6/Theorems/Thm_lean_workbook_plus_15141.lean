-- Prove2me | Theorems.Thm_lean_workbook_plus_15141
-- name    : lean_workbook_plus_15141
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/89b136dd-fa26-44bb-a195-fa7361dd4efc
-- statement:
--   Use modular arithmetic to show that if $7 \equiv -1 \pmod{4}$ and $7^2 \equiv -1 \pmod{25}$, then $7^4 \equiv 1 \pmod{100}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15141 : 7 ≡ -1 [ZMOD 4] ∧ 7 ^ 2 ≡ -1 [ZMOD 25] → 7 ^ 4 ≡ 1 [ZMOD 100]   :=  by sorry
