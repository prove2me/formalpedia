-- Prove2me | Theorems.Thm_lean_workbook_plus_67836
-- name    : lean_workbook_plus_67836
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4b0ea5bd-bcfb-45ac-8bed-12b0046e9e67
-- statement:
--   For each $n\in\mathbb{N}$ let $d_n$ denote the gcd of $n$ and $(2019-n)$. Find value of $d_1+d_2+\cdots d_{2018}+d_{2019}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67836 : ∑ i in Finset.Icc 1 2019, Nat.gcd i (2019 - i) = 6725   :=  by sorry
