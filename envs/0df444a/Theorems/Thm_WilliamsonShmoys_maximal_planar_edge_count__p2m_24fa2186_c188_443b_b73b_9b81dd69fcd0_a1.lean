-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:55.690201+00:00
-- url     : https://prove2.me/theorems/08ae3605-b2d9-40cc-aae2-fd3d57b46234
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|U|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (H : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph U, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card U) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card U := by sorry
