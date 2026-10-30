-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:12:23.170675+00:00
-- url     : https://prove2.me/theorems/a24f0493-8108-499e-80ad-7bc64688179f
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   Maximality among drawable supergraphs on the same vertex type forces at least 3n−6 edges. This isolates the maximality-to-triangulation argument. A proof route is to establish that any nontriangular face in an embedding admits an added edge while retaining a crossing-free drawing, contradicting maximality, and then apply Euler's formula. The parent combines this lower bound with the planar upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N -> M <= N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
