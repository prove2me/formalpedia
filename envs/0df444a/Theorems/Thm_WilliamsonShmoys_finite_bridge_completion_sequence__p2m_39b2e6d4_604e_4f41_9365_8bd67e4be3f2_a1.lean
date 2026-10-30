-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- name    : WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:48:33.082284+00:00
-- url     : https://prove2.me/theorems/9960b19b-62d8-4924-9bd4-14f246de67e1
-- title:
--   Finite sequence of bridge additions connects a graph
-- statement:
--   Every finite graph admits a finite sequence starting at that graph and ending at a connected graph, where each step adds exactly one edge between a pair that was unreachable before the step. This isolates the finite combinatorial construction from the predicate P. A concrete route repeatedly adds an edge across two reachability classes; each step adds a new edge, and only finitely many vertex pairs exist. The already-connected and empty-vertex cases are covered by a sequence of length zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ (n : Nat) (f : Fin (n + 1) → SimpleGraph V),
      f 0 = M ∧
      (∀ x y : V, (f (Fin.last n)).Reachable x y) ∧
      (∀ i : Fin n, ∃ x y : V,
        ¬ (f i.castSucc).Reachable x y ∧
        ∀ u v : V,
          (f i.succ).Adj u v ↔
            (f i.castSucc).Adj u v ∨
              ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by
  sorry
