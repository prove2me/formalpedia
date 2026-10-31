-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_supergraph__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- name    : WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:36.671397+00:00
-- url     : https://prove2.me/theorems/bb82f9b2-963e-4da7-bd16-87b31a6a889e
-- title:
--   Planar edge-maximal supergraph completion
-- statement:
--   Every finite drawable simple graph is contained in a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable supergraphs. Since there are finitely many simple graphs on V, maximize the number of edges among the drawable supergraphs containing H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J := by sorry
