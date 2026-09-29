-- Prove2me | Theorems.Thm_lean_workbook_plus_33301
-- name    : lean_workbook_plus_33301
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2e283a56-3d94-49e1-8215-d5796dd9f2c1
-- statement:
--   Find the sum of the digits of the number $3,333,333,333^{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33301 (x : ℕ) (hx : x = 3333333333^2) : (Nat.digits 10 x).sum = 99  :=  by sorry
