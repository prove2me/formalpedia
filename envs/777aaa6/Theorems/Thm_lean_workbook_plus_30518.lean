-- Prove2me | Theorems.Thm_lean_workbook_plus_30518
-- name    : lean_workbook_plus_30518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9e3badc3-b3ff-49bd-bb8d-36bb40c1ba64
-- statement:
--   Prove that if $a_n = n$ for all $n$, then $a_{2n} = a_n + n$ for all $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30518 (a : ℕ → ℕ) (h : ∀ n, a n = n) : ∀ n, a (2 * n) = a n + n   :=  by sorry
