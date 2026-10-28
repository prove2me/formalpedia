-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_edge_bound_extension_79011c86fe2a4d17
-- name    : WilliamsonShmoys.finite_maximal_extension_edge_bound_extension_79011c86fe2a4d17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:36:40.898653+00:00
-- url     : https://prove2.me/theorems/0b6b7123-d8f0-4f41-8b81-a8167e0110ca
-- title:
--   Maximal drawable-property extension on a finite graph
-- statement:
--   Every graph satisfying a property on a finite ordered vertex type has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension_edge_bound_extension_79011c86fe2a4d17
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    Exists fun N : SimpleGraph V => M ≤ N ∧ P N ∧
      ∀ Q : SimpleGraph V, N ≤ Q → P Q → Q ≤ N := by sorry
