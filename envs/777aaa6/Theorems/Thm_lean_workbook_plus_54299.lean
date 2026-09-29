-- Prove2me | Theorems.Thm_lean_workbook_plus_54299
-- name    : lean_workbook_plus_54299
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5934ccf9-37a1-4b2e-ab04-e43b1567ea77
-- statement:
--   Prove that $n-\phi(n) \ge d- \phi(n)$, where $d \ge 1$ and $d|n$. Equality holds if and only if $d=n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54299 (n : ℕ) (h : n ≠ 0) (d : ℕ) (hd : d ∣ n) : n - φ n ≥ d - φ n   :=  by sorry
