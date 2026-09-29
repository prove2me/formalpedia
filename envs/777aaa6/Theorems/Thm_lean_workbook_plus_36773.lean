-- Prove2me | Theorems.Thm_lean_workbook_plus_36773
-- name    : lean_workbook_plus_36773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d48d63d9-35d1-4da1-910b-bdae8d54e1d3
-- statement:
--   We know $2^{10}\equiv1\bmod 11$ so $2^{10n}\equiv1\bmod 11$ for any positive integer $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36773 (n : ℕ) : 2 ^ (10 * n) ≡ 1 [ZMOD 11]   :=  by sorry
