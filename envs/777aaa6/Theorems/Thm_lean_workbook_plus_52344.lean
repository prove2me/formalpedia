-- Prove2me | Theorems.Thm_lean_workbook_plus_52344
-- name    : lean_workbook_plus_52344
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/2a198ffa-ca50-4482-8ff7-1289681c1cb6
-- statement:
--   Prove that each positive integer is in exactly one of the sets $A_{m,i} = \{x : x \equiv i \mod 2^m - 1\}$, where $0 \leq i < 2^m - 1$ and $m$ is a positive integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52344 (m : ℕ) (i : ℕ) (x : ℕ) : (x ≡ i [ZMOD 2 ^ m - 1]) ↔ (x ∈ {y : ℕ | y ≡ i [ZMOD 2 ^ m - 1]})   :=  by sorry
