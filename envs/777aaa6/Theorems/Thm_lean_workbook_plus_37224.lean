-- Prove2me | Theorems.Thm_lean_workbook_plus_37224
-- name    : lean_workbook_plus_37224
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/df03788c-1394-490a-974d-0f554a506d7b
-- statement:
--   Given a real number $\varepsilon \in (0,1)$ , prove that, for all large enough positive integers $N$ , there exists a suitable set of size at least $\varepsilon N$ , each element of which is at most $N$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37224 (N : ℕ) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ A : Finset ℕ, (A.card ≥ ε * N ∧ ∀ x ∈ A, x ≤ N)   :=  by sorry
