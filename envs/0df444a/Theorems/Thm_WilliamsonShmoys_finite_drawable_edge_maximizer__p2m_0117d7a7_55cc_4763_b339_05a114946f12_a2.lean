-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_edge_maximizer__p2m_0117d7a7_55cc_4763_b339_05a114946f12_a2
-- name    : WilliamsonShmoys.finite_drawable_edge_maximizer__p2m_0117d7a7_55cc_4763_b339_05a114946f12_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:14.59521+00:00
-- url     : https://prove2.me/theorems/f7fbc9fb-9397-4a97-baf6-b642e02aafec
-- title:
--   Finite drawable edge maximizer
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph whose edge set has maximum cardinality among drawable supergraphs of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_drawable_edge_maximizer__p2m_0117d7a7_55cc_4763_b339_05a114946f12_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
