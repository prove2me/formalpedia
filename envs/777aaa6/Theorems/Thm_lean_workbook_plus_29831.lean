-- Prove2me | Theorems.Thm_lean_workbook_plus_29831
-- name    : lean_workbook_plus_29831
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/45c15257-ea8c-48f5-a1d3-62f9b1b348e8
-- statement:
--   For each $n\in\mathbb{N}$ let $d_n$ denote the gcd of $n$ and $(2019-n)$. Find value of $d_1+d_2+\cdots d_{2018}+d_{2019}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29831 : ∑ i in Finset.range 2019, Nat.gcd i (2019 - i) = 6725   :=  by sorry
