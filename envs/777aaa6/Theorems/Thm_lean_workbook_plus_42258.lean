-- Prove2me | Theorems.Thm_lean_workbook_plus_42258
-- name    : lean_workbook_plus_42258
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8a6b96f7-02d7-4027-9ec2-a9c1042352aa
-- statement:
--   It can be shown by induction that $x_n\in (a,2a)\ \ \forall n\ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42258 (a : ℝ) (x : ℕ → ℝ) (hx: x 0 = a) (hn: ∀ n:ℕ, x (n+1) = 2 * x n - a) : ∀ n:ℕ, x n ∈ Set.Ioo a (2 * a)   :=  by sorry
