-- Prove2me | Theorems.Thm_lean_workbook_plus_76567
-- name    : lean_workbook_plus_76567
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/38fe0d39-3fb0-4b5d-92ed-576ed37c8b7a
-- statement:
--   If $p=5k-1$, prove that $5\mid p+26$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76567 (p : ℤ) (hp : p = 5 * k - 1) : p + 26 ≡ 0 [ZMOD 5]   :=  by sorry
