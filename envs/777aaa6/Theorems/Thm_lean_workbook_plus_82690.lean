-- Prove2me | Theorems.Thm_lean_workbook_plus_82690
-- name    : lean_workbook_plus_82690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3cd769d5-4c09-4910-8c4b-4437a824f4ad
-- statement:
--   Let M be a symmetric matrix of order n such that $ M^k=0 $ for all k belongs to N. Show that M=0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82690 (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M) (hMk : ∀ k : ℕ, M ^ k = 0) : M = 0   :=  by sorry
