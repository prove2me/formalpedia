-- Prove2me | Theorems.Thm_lean_workbook_plus_43714
-- name    : lean_workbook_plus_43714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e247c636-e6b5-417e-ba60-d5e9c9364435
-- statement:
--   Prove that for any natural $n$, there are nonnegative integers $q, r$ such that $0 \le r < 3$ and $n = 3q + r$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43714 (n : ℕ) : ∃ q r : ℕ, 0 ≤ r ∧ r < 3 ∧ n = 3 * q + r   :=  by sorry
