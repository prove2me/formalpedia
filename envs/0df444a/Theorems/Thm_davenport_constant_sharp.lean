-- Prove2me | Theorems.Thm_davenport_constant_sharp
-- name    : davenport_constant_sharp
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:46:58.327984+00:00
-- url     : https://prove2.me/theorems/73954892-92a9-460e-ac08-5efea6035c5f
-- title:
--   Sharpness: the Davenport constant of $\mathbb{Z}/n\mathbb{Z}$ is at least $n$
-- statement:
--   The Davenport constant of the cyclic group $\mathbb{Z}/n\mathbb{Z}$ is at least $n$: the sequence of $n-1$ ones has no nonempty subsequence with sum zero.
--
--   $$\exists?\ \varnothing \ne S \subseteq \{0, \dots, n-2\} \text{ with } \sum_{k \in S} 1 = 0 \text{ in } \mathbb{Z}/n\mathbb{Z}\quad\text{— never.}$$
--
--   Together with `davenport_zero_sum` (every sequence of $n$ elements has a nonempty zero-sum subsequence), this pins the Davenport constant of $C_n$ at exactly $n$. The argument: a nonempty subsequence of the constant sequence $1, 1, \dots, 1$ sums to its cardinality $c$ with $1 \le c \le n - 1$, and $c \cdot 1 = 0$ in $\mathbb{Z}/n\mathbb{Z}$ only when $n \mid c$, which cannot happen for $0 < c < n$.
--
--   **Formalization Note** The sequence is the constant function with value `(1 : ZMod n)` restricted to the first `n - 1` indices via `t ⊆ Finset.range (n - 1)`; the vanishing of the sum is converted to `n ∣ t.card` via `ZMod.natCast_eq_zero_iff`.
-- source:
--   Classical zero-sum example; see W. D. Gao, A. Geroldinger, Zero-sum problems in finite abelian groups: a survey, Expo. Math. 24 (2006), 337-369 (D(C_n) = n)

import Mathlib

theorem davenport_constant_sharp (n : ℕ) (hn : 0 < n) :
    ¬ ∃ t : Finset ℕ, t.Nonempty ∧ t ⊆ Finset.range (n - 1) ∧ ∑ k ∈ t, (1 : ZMod n) = 0 := by sorry
