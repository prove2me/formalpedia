-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:31:51.864501+00:00
-- url     : https://prove2.me/theorems/dcbc2578-61e6-4916-944b-fcd42b3708ca
-- title:
--   A drawable graph has an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable supergraph that is maximal under inclusion among drawable supergraphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        ∀ H : SimpleGraph V, U ≤ H → HasPlanarDrawingOn H → H ≤ U := by sorry
