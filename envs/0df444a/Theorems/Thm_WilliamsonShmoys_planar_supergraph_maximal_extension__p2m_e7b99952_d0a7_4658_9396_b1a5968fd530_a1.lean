-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:11.941344+00:00
-- url     : https://prove2.me/theorems/4d37fe7f-2e72-452b-8439-d9da71f76f12
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph V,
        N.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = N.edgeSet := by sorry
