-- Prove2me | Theorems.Thm_lean_workbook_plus_1391
-- name    : lean_workbook_plus_1391
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2bf46cd7-2716-4ecb-ba3d-f98f0f8a2099
-- statement:
--   Prove that all perfect squares are congruent to $1 \pmod{4}$ or $0 \pmod{4}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1391 {n : ℤ} (h : n = m ^ 2) : n ≡ 0 [ZMOD 4] ∨ n ≡ 1 [ZMOD 4]   :=  by sorry
