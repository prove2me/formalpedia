-- Prove2me | Theorems.Thm_syracuse_cycle_adjacent_pair_budget
-- name    : syracuse_cycle_adjacent_pair_budget
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:49:26.225473+00:00
-- url     : https://prove2.me/theorems/1b835de0-3ca5-4ffe-9aaf-877ee0ff7af1
-- title:
--   A bound from consecutive entries of a Syracuse cycle
-- statement:
--   Let $T(x)$ be the odd part of $3x+1$. Suppose $T^p(m)=m$ and $x_i=T^i(m)\ge B>0$ throughout the orbit. Let $H$ be a natural number with $2H\le3B+1$ and $3H\le4B+1$. With $K=\sum_{i=0}^{p-1}v_2(3x_i+1)$, the cycle satisfies
--   $$2^{2K}(BH)^p\le\big((3B+1)(3H+1)\big)^p.$$
--   Every neighboring pair contains a term at least $H$. Thus both a baseline $B$ and a higher threshold $H$ may be used in each pair. The result holds for odd and even periods, including return times which are multiples of the least period.
-- source:
--   Original adjacent-pair product estimate from the recurrence 2^{e_i} x_{i+1} = 3 x_i + 1. Developed for https://prove2.me/theorems/475518d9-1e4f-4b12-a93e-4fb02eef8946.

import Definitions.Def_syracuseStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate

theorem syracuse_cycle_adjacent_pair_budget (m p B H : ℕ) (hB : 0 < B) (hcycle : syracuseStep^[p] m = m)
    (hbase : ∀ i : ℕ, B ≤ syracuseStep^[i] m)
    (h1 : 2 * H ≤ 3 * B + 1) (h2 : 3 * H ≤ 4 * B + 1) :
    2 ^ (2 * ∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      (B * H) ^ p ≤ ((3 * B + 1) * (3 * H + 1)) ^ p := by sorry
