-- Prove2me | Theorems.Thm_lean_workbook_plus_19450
-- name    : lean_workbook_plus_19450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/975cde58-f150-4846-8cd2-9f2a8ff4bb79
-- statement:
--   Prove that $a^2\equiv1(\bmod2)$ for any odd number $a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19450 {a : ℤ} (h : a%2 = 1) : a ^ 2 ≡ 1 [ZMOD 2]   :=  by sorry
