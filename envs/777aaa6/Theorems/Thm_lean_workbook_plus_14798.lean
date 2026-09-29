-- Prove2me | Theorems.Thm_lean_workbook_plus_14798
-- name    : lean_workbook_plus_14798
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a38bc76c-7e75-40b8-8d00-13dcdd8768ae
-- statement:
--   If $a\equiv 2\mod 3$ then $a-1\equiv 1\mod 3$ and $2a+1\equiv 2\mod 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14798 : ∀ a : ℤ, a ≡ 2 [ZMOD 3] → a - 1 ≡ 1 [ZMOD 3] ∧ 2 * a + 1 ≡ 2 [ZMOD 3]   :=  by sorry
