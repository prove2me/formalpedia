-- Prove2me | Theorems.Thm_lean_workbook_plus_10087
-- name    : lean_workbook_plus_10087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/205af9a8-bd7a-44d8-bde0-b5d4cd72db3b
-- statement:
--   Prove that $ f(n) = 1 - n$ for nonnegative integers $ n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10087 (f : ℕ → ℕ) (hf: f 0 = 1) (hf2 : ∀ n, f (n + 1) = f n - 1) : ∀ n, f n = 1 - n   :=  by sorry
