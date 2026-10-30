-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:36:22.447768+00:00
-- url     : https://prove2.me/theorems/d65752b0-c280-4c98-926b-0ae69c395723
-- title:
--   Maximal planar drawing edge count lower bound
-- statement:
--   A graph maximal under planar-drawable supergraphs on at least three vertices has at least `3 * |V| - 6` edges. This removes the lower-bound half of the target. Extend the drawing to a triangulation using the same finite vertex set; the extension is a drawable supergraph, so `hMax` identifies it with `M`, and Euler's formula for the triangulation gives the bound. The extension and Euler count are the remaining core obligations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_fe266be1_b394_4319_ae10_b52cb17a5e91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
