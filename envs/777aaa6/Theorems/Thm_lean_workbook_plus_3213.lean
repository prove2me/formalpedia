-- Prove2me | Theorems.Thm_lean_workbook_plus_3213
-- name    : lean_workbook_plus_3213
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dbeba7e9-ee79-4a9d-b682-efc7749673bb
-- statement:
--   Prove that $n^{2}\equiv 1\pmod{5}\iff n\equiv\pm 1\pmod{5}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3213 (n : ℤ) : n ^ 2 ≡ 1 [ZMOD 5] ↔ n ≡ 1 [ZMOD 5] ∨ n ≡ -1 [ZMOD 5]   :=  by sorry
