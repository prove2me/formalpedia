-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
-- name    : WilliamsonShmoys.maximal_drawable_extension__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:51:59.95337+00:00
-- url     : https://prove2.me/theorems/0b2a65e7-c543-4720-a444-78ba2c303f5d
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex set of size at least three is contained in a drawable supergraph on the same vertex set that is maximal among drawable supergraphs; its edge count is at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      L.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
