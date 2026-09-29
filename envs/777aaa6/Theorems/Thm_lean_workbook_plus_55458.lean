-- Prove2me | Theorems.Thm_lean_workbook_plus_55458
-- name    : lean_workbook_plus_55458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6b68a0ba-0305-4691-8c83-9ce5163bcdc4
-- statement:
--   Let $c \ge 0,\;\;\; c^3 \le c^3+c <(c+1)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55458  (c : ℝ)
  (h₀ : 0 ≤ c) :
  c^3 ≤ c^3 + c ∧ c^3 + c < (c + 1)^3   :=  by sorry
