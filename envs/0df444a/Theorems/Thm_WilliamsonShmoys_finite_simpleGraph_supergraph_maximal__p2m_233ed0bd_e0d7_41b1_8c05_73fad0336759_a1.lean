-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_supergraph_maximal__p2m_233ed0bd_e0d7_41b1_8c05_73fad0336759_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_233ed0bd_e0d7_41b1_8c05_73fad0336759_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:22.970003+00:00
-- url     : https://prove2.me/theorems/7fc18aad-d07a-49bb-b01c-abff1eddf2b3
-- title:
--   Maximal predicate-satisfying supergraph on a finite vertex type
-- statement:
--   If P holds for a graph H on a finite vertex type, then H has a P-satisfying supergraph that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_233ed0bd_e0d7_41b1_8c05_73fad0336759_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hH : P H) :
    exists J : SimpleGraph V,
      And (P J)
        (And (H <= J)
          (forall K : SimpleGraph V,
            P K -> J <= K -> K <= J)) := by sorry
