-- Prove2me | Theorems.Thm_lean_workbook_plus_5314
-- name    : lean_workbook_plus_5314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/eafb5b30-2cb0-4708-a359-3b1e19a5a3d5
-- statement:
--   Let $k\in \mathbb{Z^+},$ $m$ is an odd natural number. Prove that exists $n\in \mathbb{Z^+}$ such that $2^k\mid n^n-m$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5314 (k m : ℕ) (hm : Odd m) : ∃ n : ℕ, 2 ^ k ∣ n ^ n - m   :=  by sorry
