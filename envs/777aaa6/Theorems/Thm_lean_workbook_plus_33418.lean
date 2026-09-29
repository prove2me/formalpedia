-- Prove2me | Theorems.Thm_lean_workbook_plus_33418
-- name    : lean_workbook_plus_33418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/17344a78-886d-4ae7-998f-fc8f272cbd20
-- statement:
--   Compute: \n $$\binom{10}{3} \times \binom{5}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33418 (h₁ : 3 ≤ 10) (h₂ : 2 ≤ 5) : (Nat.choose 10 3) * (Nat.choose 5 2) = 1200   :=  by sorry
