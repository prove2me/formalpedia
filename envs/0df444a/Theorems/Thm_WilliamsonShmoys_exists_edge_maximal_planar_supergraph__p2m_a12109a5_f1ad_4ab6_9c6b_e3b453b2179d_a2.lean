-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:15.699907+00:00
-- url     : https://prove2.me/theorems/8824e35c-b427-4577-adf2-2966f46879ec
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on an ordered vertex type has a drawable supergraph that is maximal under inclusion among drawable supergraphs on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by sorry
