-- Prove2me | Theorems.Thm_lean_workbook_plus_55225
-- name    : lean_workbook_plus_55225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4fbafde2-c78a-4476-8ea8-a6abad21433e
-- statement:
--   prove that $n^5$ $\equiv n$ (mod 10)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55225 : ∀ n : ℕ, n^5 ≡ n [ZMOD 10]   :=  by sorry
