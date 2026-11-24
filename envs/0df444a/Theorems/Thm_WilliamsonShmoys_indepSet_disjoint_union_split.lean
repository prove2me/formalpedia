-- Prove2me | Theorems.Thm_WilliamsonShmoys_indepSet_disjoint_union_split
-- name    : WilliamsonShmoys.indepSet_disjoint_union_split
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T11:23:29.394537+00:00
-- url     : https://prove2.me/theorems/f2292f0e-c53a-4a13-b1db-be693d7a8da7
-- title:
--   Optimal independent sets of a disjoint union are optimal in each copy
-- statement:
--   Let $H_0,\dots,H_{m-1}$ be graphs on $\{0,\dots,n-1\}$, let $U$ be their disjoint union on $\{0,\dots,m-1\}\times\{0,\dots,n-1\}$, and let $w$ be a real weight function on the vertices of $U$. Let $A$ be an independent set of $U$ of maximum weight among all independent sets of $U$. Then, for every copy $j$ and every independent set $S$ of $H_j$,
--
--   $$\sum_{a\in S} w(j,a)\;\le\;\sum_{x\in A,\;x_1=j} w(x).$$
--
--   In words, the part of an optimal independent set of a disjoint union that lies in one copy is optimal for that copy. This lets one call of an exact maximum-weight-independent-set solver, run on the disjoint union of $k$ instances, give optimal answers for all $k$ instances at once. That is the basis of the single-call RAM implementation of Baker's shifting technique.
--
--   **Formalization Note.** $U$ is `SimpleGraph.fromRel (fun u v => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)` on `Fin m × Fin n`. Weights are arbitrary reals; no sign assumption is needed.
-- source:
--   Standard; used for the RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.indepSet_disjoint_union_split {m n : ℕ} (H : Fin m → SimpleGraph (Fin n)) (w : Fin m × Fin n → ℝ)
    (A : Finset (Fin m × Fin n))
    (hA : (SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)).IsIndepSet
      (A : Set (Fin m × Fin n)))
    (hopt : ∀ S : Finset (Fin m × Fin n),
      (SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)).IsIndepSet
        (S : Set (Fin m × Fin n)) →
      ∑ x ∈ S, w x ≤ ∑ x ∈ A, w x)
    (j : Fin m) (S : Finset (Fin n)) (hS : (H j).IsIndepSet (S : Set (Fin n))) :
    ∑ a ∈ S, w (j, a) ≤ ∑ x ∈ A.filter (fun x => x.1 = j), w x := by sorry
