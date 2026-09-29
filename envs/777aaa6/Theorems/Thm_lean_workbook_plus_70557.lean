-- Prove2me | Theorems.Thm_lean_workbook_plus_70557
-- name    : lean_workbook_plus_70557
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/388e745d-64df-42b6-9e4a-40ab50a31fcb
-- statement:
--   Prove by induction that for any positive integer n, the following property holds: $(a_1, ...,a_{n})= (b_1, ...,b_{n}) \Leftrightarrow a_{i}= b_{i} $ for each $i$ , $1 \leq i \leq n$. The ordered pair is defined as $(a, b)= \{{a}, \{a, b\} \}$ and the (k+1) tuple is defined as $(a_1, ...,a_{k}, a_{k+1}) = ((a_1, ...a_{k}), a_{k+1})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70557 (n : ℕ) (a b : Fin n → ℕ) : a = b ↔ ∀ i, a i = b i   :=  by sorry
