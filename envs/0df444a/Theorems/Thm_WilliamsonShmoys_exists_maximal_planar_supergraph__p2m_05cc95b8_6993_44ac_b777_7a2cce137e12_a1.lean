-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:40.20407+00:00
-- url     : https://prove2.me/theorems/1bb19ac6-452e-443b-a585-944a9ce0af63
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on that same vertex type. This removes the finite maximal-choice step from the parent; prove it by maximizing edge count among the finite collection of drawable supergraphs containing L. The collection is nonempty because it contains L. This claim makes no connectedness assumption.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
