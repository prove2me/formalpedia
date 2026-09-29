-- Prove2me | Theorems.Thm_lean_workbook_plus_62665
-- name    : lean_workbook_plus_62665
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f508b6c6-4816-4404-8fe7-4d25f0d9d3dd
-- statement:
--   Prove that $(n-1)|(n^{k}-1)$ for $n\geq2$ and any positive integer $k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62665 (n : ℕ) (k : ℕ) (hn : 2 ≤ n) : n - 1 ∣ n^k - 1   :=  by sorry
