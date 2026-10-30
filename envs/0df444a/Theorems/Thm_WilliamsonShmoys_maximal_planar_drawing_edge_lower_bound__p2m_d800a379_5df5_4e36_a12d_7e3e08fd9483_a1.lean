-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:59:45.379107+00:00
-- url     : https://prove2.me/theorems/292cccde-9238-49dd-bff4-dbc6d5d73c71
-- title:
--   Edge lower bound for a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
