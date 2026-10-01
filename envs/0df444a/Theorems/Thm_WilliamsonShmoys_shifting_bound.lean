-- Prove2me | Theorems.Thm_WilliamsonShmoys_shifting_bound
-- name    : WilliamsonShmoys.shifting_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-30T13:51:34.03221+00:00
-- url     : https://prove2.me/theorems/c0f90b67-71b5-405b-9c34-27d3512dc74d
-- title:
--   Shifting lemma: the best of $k$ shifted optima is a $(1-1/k)$-approximation
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$, let $w : V \to \mathbb{R}$ be arbitrary real weights, let $k \ge 1$, and let $c : V \to \mathbb{N}$ be any labelling (in Baker's technique, the breadth-first-search level). For $0 \le j < k$ write $V_j = \{v : c(v) \equiv j \pmod k\}$. Suppose a finite set $A \subseteq V$ has weight at least that of every independent set avoiding some class, i.e.
--
--   $$\sum_{v\in S} w(v) \le \sum_{v \in A} w(v) \quad \text{for every } j<k \text{ and every independent } S \text{ with } S\cap V_j=\emptyset.$$
--
--   Then for every finite independent set $S$,
--
--   $$\Bigl(1-\frac1k\Bigr)\sum_{v\in S} w(v) \le \sum_{v\in A} w(v).$$
--
--   This is the averaging argument behind Baker's shifting technique in the proof of Theorem 10.11: the $k$ sets $S\setminus V_j$ are independent and together cover every vertex of $S$ exactly $k-1$ times, so their total weight is $(k-1)w(S)$ and one of them has weight at least $(1-1/k)w(S)$.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. (the averaging step: some shift loses at most a 1/k fraction of the optimum)

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators

namespace WilliamsonShmoys
theorem shifting_bound {V : Type} (G : SimpleGraph V) (w : V → ℝ) (c : V → ℕ)
    (k : ℕ) (hk : 0 < k) (A : Finset V)
    (hA : ∀ j < k, ∀ S : Finset V, G.IsIndepSet (S : Set V) →
      (∀ v ∈ S, c v % k ≠ j) → ∑ i ∈ S, w i ≤ ∑ i ∈ A, w i)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    (1 - 1 / (k : ℝ)) * ∑ i ∈ S, w i ≤ ∑ i ∈ A, w i := by sorry
end WilliamsonShmoys
