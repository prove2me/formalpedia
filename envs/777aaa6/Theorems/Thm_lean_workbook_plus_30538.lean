-- Prove2me | Theorems.Thm_lean_workbook_plus_30538
-- name    : lean_workbook_plus_30538
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/598c4a3f-b5b9-466c-8c91-4e853d5c389d
-- statement:
--   Prove that $ p\leq a\leq b\leq q, bp-aq\leq 0, bq-pa\geq 0$ implies $ (bp-aq)(bq-pa)\leq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30538 : ∀ a b p q : ℝ, p ≤ a ∧ a ≤ b ∧ b ≤ q ∧ bp - aq ≤ 0 ∧ bq - pa ≥ 0 → (bp - aq) * (bq - pa) ≤ 0   :=  by sorry
