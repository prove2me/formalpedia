-- Prove2me | Theorems.Thm_BookSixth_bregman_minc_geometric_mean
-- name    : BookSixth.bregman_minc_geometric_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T15:34:54.470204+00:00
-- url     : https://prove2.me/theorems/b2f46b2c-71e4-4726-9015-296efd00d99b
-- title:
--   Bregman-Minc: geometric mean of ordering weights
-- statement:
--   Let $A$ be an $n$ by $n$ zero-one matrix with positive row sums $d_i$, and let $\sigma$ be a compatible permutation, meaning $A_{i,\sigma(i)}=1$ for every row. For a row ordering $\pi$, let $q(A,\sigma,\pi)$ be the product over rows of the reciprocal number of admissible columns still available along the assignment prescribed by $\sigma$. Then
--
--   $$\left(\prod_{\pi\in S_n}q(A,\sigma,\pi)\right)^{1/n!}=\prod_i(d_i!)^{-1/d_i}.$$
--
--   This exact geometric mean isolates the permutation-counting part of the ordering-weight lower bound from the arithmetic-geometric mean inequality. The statement includes $n=0$, where the empty row product and the unique ordering weight are both one.
-- source:
--   Source-derived intermediate identity for BookSixth.bregman_minc_claimB, https://prove2.me/api/v1/theorems/c8169994-87d3-4602-967b-9d68d4da794f, specifically the available-count product identity described in its authoritative natural-language statement. Uses the exact definitions at https://prove2.me/api/v1/theorems/52d231bb-cd49-4d96-840a-b424962608e2. This geometric-mean formulation is an algebraic consequence of that counting identity, not a separately numbered quotation from Radhakrishnan (1997).

import Mathlib
import Definitions.Def_BregmanMincWeights
open scoped BigOperators
open BregmanMincWeights

theorem BookSixth.bregman_minc_geometric_mean (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1) (hrows : ∀ i, 0 < ∑ j, A i j) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ aSys A) : (∏ π : Equiv.Perm (Fin n), qW A σ π) ^ ((n.factorial : ℝ)⁻¹) = ∏ i : Fin n, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^ (-(1 : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) := by sorry
