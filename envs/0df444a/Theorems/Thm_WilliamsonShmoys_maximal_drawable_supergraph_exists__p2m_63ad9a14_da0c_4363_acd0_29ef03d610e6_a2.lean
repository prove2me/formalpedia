-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:29.494254+00:00
-- url     : https://prove2.me/theorems/14e607d3-c2c5-4591-b3a8-62073f54043e
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion. Since there are finitely many simple graphs on the vertex type, maximize edge count among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L ≤ M ∧
      (∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        M ≤ N →
        N = M) := by
  sorry
