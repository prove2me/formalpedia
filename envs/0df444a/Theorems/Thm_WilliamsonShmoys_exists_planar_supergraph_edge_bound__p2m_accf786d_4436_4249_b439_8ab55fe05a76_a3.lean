-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a3
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T04:54:59.363633+00:00
-- url     : https://prove2.me/theorems/d7d089da-42dd-4fb9-9d5f-fd887681c907
-- title:
--   Planar supergraph edge lower bound
-- statement:
--   Every graph on at least three finite, linearly ordered vertices with the supplied planar drawing has a planar supergraph on the same vertices with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet <= M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
