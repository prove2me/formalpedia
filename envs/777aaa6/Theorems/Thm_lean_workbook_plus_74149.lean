-- Prove2me | Theorems.Thm_lean_workbook_plus_74149
-- name    : lean_workbook_plus_74149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2114bc94-82ec-4e92-85d9-cbc6873d7cc7
-- statement:
--   $x=32$ and $y=32^3-32\times 1000=768$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74149 (x y : ℕ) (hx : x = 32) (hy : y = 32^3 - 32 * 1000) : x = 32 ∧ y = 768   :=  by sorry
