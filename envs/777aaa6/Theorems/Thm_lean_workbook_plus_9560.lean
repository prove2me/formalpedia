-- Prove2me | Theorems.Thm_lean_workbook_plus_9560
-- name    : lean_workbook_plus_9560
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/074bc1c1-c943-4112-a684-214d0e4eb546
-- statement:
--   Prove that if $ x + y + z = 6$ and $ xy + yz + zx = 9$ ( $ x,y,z\in\mathbb{R}$ ) then $ 0\le x,y,z\le 4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9560 (x y z : ℝ) (h₁ : x + y + z = 6) (h₂ : x * y + y * z + z * x = 9) : 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4 ∧ 0 ≤ z ∧ z ≤ 4   :=  by sorry
