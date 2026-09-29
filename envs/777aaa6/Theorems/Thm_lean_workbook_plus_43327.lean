-- Prove2me | Theorems.Thm_lean_workbook_plus_43327
-- name    : lean_workbook_plus_43327
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/577cd70d-ea4b-4fa8-99c0-2c72e7f0a733
-- statement:
--   Prove that in $Z_{10}$ we have $7^{4n+1}=7$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43327 (n : ℕ) : 7 ^ (4 * n + 1) ≡ 7 [ZMOD 10]   :=  by sorry
