-- Prove2me | Theorems.Thm_lean_workbook_plus_34502
-- name    : lean_workbook_plus_34502
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c5c5c5b3-62d8-47e4-8692-5a5c9cbca5ca
-- statement:
--   Consider the ends of the ruler as marks too. With $n$ marks, we can measure $\binom{n}{2}$ lengths, since we can (only) measure distances between any pair of marks. So we need $\binom{n}{2} \ge 16$ , giving $n \ge 7$ . In other words, we need 5 extra marks besides the endpoints.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34502  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : n.choose 2 ≥ 16) :
  5 ≤ n - 2   :=  by sorry
