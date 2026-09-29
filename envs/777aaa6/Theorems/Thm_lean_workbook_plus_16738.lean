-- Prove2me | Theorems.Thm_lean_workbook_plus_16738
-- name    : lean_workbook_plus_16738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/85f20d15-0562-473c-ae8e-0d43a134962a
-- statement:
--   Prove that for all positive integers $ x$ and all integers $ n$ relatively prime to $ x$ , there are infinitely many integers $ k$ such that $ x^k - 1$ is a multiple of $ n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16738 (x n : ℤ) (hpos : 0 < x) (hrelprime : (x.gcd n) = 1) : ∃ k, n ∣ x^k - 1   :=  by sorry
