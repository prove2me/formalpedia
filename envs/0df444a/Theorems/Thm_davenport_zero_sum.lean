-- Prove2me | Theorems.Thm_davenport_zero_sum
-- name    : davenport_zero_sum
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:23:32.496694+00:00
-- url     : https://prove2.me/theorems/a1d8efd2-059e-46fc-88d0-c12859cd32b8
-- title:
--   Davenport's theorem: the Davenport constant of $\mathbb{Z}/n\mathbb{Z}$ is at most $n$
-- statement:
--   **Davenport's theorem.** Every sequence of $n$ elements of the cyclic group $\mathbb{Z}/n\mathbb{Z}$ has a nonempty subsequence whose sum is zero: the Davenport constant of $C_n$ is at most $n$.
--
--   $$\forall\ n \ge 1,\ \forall\ a_0, \dots, a_{n-1} \in \mathbb{Z}/n\mathbb{Z},\quad \exists\ \varnothing \ne S \subseteq \{0, \dots, n-1\},\quad \sum_{k \in S} a_k = 0.$$
--
--   The bound is sharp — the Davenport constant of $C_n$ equals $n$ exactly, since the sequence of $n - 1$ ones has no nonempty zero-sum subsequence (a nonempty partial sum equals $k \cdot 1$ for some $1 \le k \le n - 1$, which is zero only at multiples of $n$).
--
--   Together with the Erdős–Ginzburg–Ziv theorem (constant $2n - 1$ for the version requiring subsequences of length exactly $n$), this is the foundation of zero-sum theory in finite abelian groups. The proof is the classical partial-sums pigeonhole: the $n + 1$ initial sums $p_k = a_0 + \cdots + a_{k-1}$, $0 \le k \le n$, cannot all be distinct in a group of $n$ elements, and from $p_i = p_j$ with $i < j$ the interval $S = \{i, \dots, j-1\}$ is a nonempty zero-sum subsequence.
--
--   **Formalization Note** The sequence is a function `ℕ → ZMod n` restricted to the first `n` indices via `t ⊆ Finset.range n`; the subsequence is a `Finset ℕ`.
-- source:
--   H. Davenport, 1966 (the Davenport constant); statement and partial-sums proof as in W. D. Gao, A. Geroldinger, Zero-sum problems in finite abelian groups: a survey, Expo. Math. 24 (2006), 337-369 (D(C_n) = n)

import Mathlib

theorem davenport_zero_sum (n : ℕ) (hn : 0 < n) (a : ℕ → ZMod n) :
    ∃ t : Finset ℕ, t.Nonempty ∧ t ⊆ Finset.range n ∧ ∑ k ∈ t, a k = 0 := by sorry
