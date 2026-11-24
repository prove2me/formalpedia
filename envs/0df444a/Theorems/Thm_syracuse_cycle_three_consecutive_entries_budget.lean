-- Prove2me | Theorems.Thm_syracuse_cycle_three_consecutive_entries_budget
-- name    : syracuse_cycle_three_consecutive_entries_budget
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:57:54.35589+00:00
-- url     : https://prove2.me/theorems/b41a66d1-5e1e-417d-8bb9-50b7baa86285
-- title:
--   A product bound from three consecutive Syracuse orbit entries
-- statement:
--   Let $T(x)$ be the odd part of $3x+1$, and suppose $T^p(m)=m$. Let $b>0$ be an integer such that every orbit entry $x_i=T^i(m)$ is at least $8b$. Write $K=\sum_{i=0}^{p-1}v_2(3x_i+1)$, $D=(8b)(9b)(12b)$ and $A=(24b+1)(27b+1)(36b+1)$. Then
--   $$2^{3K}D^p\le A^p.$$
--   In every three consecutive entries the smallest is at least $8b$, the middle one at least $9b$, and the largest at least $12b$ when ordered by size. Multiplying the resulting inequalities over all cyclic triples yields the bound.
-- source:
--   Original estimate from the exact one-step and two-step Syracuse recurrences. Strengthens the window method used in https://prove2.me/theorems/1b835de0-3ca5-4ffe-9aaf-877ee0ff7af1 for the residual problem https://prove2.me/theorems/055539bb-518e-4e7d-869c-639609b16db6.

import Definitions.Def_syracuseStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate

theorem syracuse_cycle_three_consecutive_entries_budget (m p b : ℕ) (hb : 0 < b) (hcycle : syracuseStep^[p] m = m)
    (hbase : ∀ i : ℕ, 8 * b ≤ syracuseStep^[i] m) :
    2 ^ (3 * ∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      ((8 * b) * (9 * b) * (12 * b)) ^ p ≤
        ((3 * (8 * b) + 1) * (3 * (9 * b) + 1) * (3 * (12 * b) + 1)) ^ p := by sorry
