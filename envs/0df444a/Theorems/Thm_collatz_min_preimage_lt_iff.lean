-- Prove2me | Theorems.Thm_collatz_min_preimage_lt_iff
-- name    : collatz_min_preimage_lt_iff
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:12:41.782627+00:00
-- url     : https://prove2.me/theorems/5cb09342-d23c-4138-8b48-6d2776fa6793
-- title:
--   Exactness of the minimum preimage in the bounded Collatz inverse tree
-- statement:
--   Let $C$ be the classical Collatz map, let $y>0$ be a target value, and let $m_d(y)$ denote the minimum returned by the depth-$d$ inverse-tree recurrence. For a threshold $n$, the recurrence returns a value strictly below $n$ exactly when there is a positive start below $n$ reaching $y$ in at most $d$ steps:
--
--   $$
--   m_d(y)<n\quad\Longleftrightarrow\quad
--   \exists k,b\in\mathbb N,\quad 0<k<n,\quad b\le d,\quad C^b(k)=y .
--   $$
--
--   This characterizes the test in both directions. A successful test certifies a smaller start, and a failed test rules out all witnesses within the prescribed depth.
-- source:
--   D. Applegate and J. C. Lagarias, Lower bounds for the total stopping time of 3X+1 iterates, Math. Comp. 72 (2003), Section 2 (inverse trees), https://arxiv.org/abs/math/0103054. The bounded inverse tree here uses the ordinary Collatz map.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_min_preimage_lt_iff (depth y n : ℕ) (hy : 0 < y) :
    collatzMinPreimage depth y < n ↔
      ∃ k b : ℕ, 0 < k ∧ k < n ∧ b ≤ depth ∧ collatzStep^[b] k = y := by
  sorry
