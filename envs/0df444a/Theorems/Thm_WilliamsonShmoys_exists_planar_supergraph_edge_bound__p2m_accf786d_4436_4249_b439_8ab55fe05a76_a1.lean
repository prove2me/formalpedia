-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T04:21:13.930174+00:00
-- url     : https://prove2.me/theorems/f9e6df35-66b2-40ec-8149-0e892b75a930
-- title:
--   A planar drawing extends to a dense planar supergraph
-- statement:
--   Every crossing-free drawing on at least three vertices extends, on the same vertex set, to a planar supergraph with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_bound__p2m_accf786d_4436_4249_b439_8ab55fe05a76_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V,
      L.edgeSet <= M.edgeSet /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
