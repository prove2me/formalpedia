-- Prove2me | Theorems.Thm_lean_workbook_plus_68616
-- name    : lean_workbook_plus_68616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f34ff158-3036-4046-953c-a2d5ae0df98f
-- statement:
--   How many sequences of natural number such that $1 \le {a_1}<{a_2} <.....<{a_k}\le n$ and ${a_i} \equiv {i} \pmod {2} \forall i $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68616 (n k : ℕ) : n ≥ k → ∃ a : ℕ → ℕ, (∀ i : ℕ, 1 ≤ i ∧ i ≤ k → a i ≡ i [ZMOD 2] ∧ a i < a (i + 1)) ∧ a k ≤ n   :=  by sorry
