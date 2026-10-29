-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:37:27.920213+00:00
-- url     : https://prove2.me/theorems/b7437c67-f19b-46b7-abfb-8f1126c280d3
-- title:
--   Edge lower bound from drawable maximality
-- statement:
--   A drawable graph with at least three vertices that maximizes edge count among drawable supergraphs has at least 3|V|−6 edges. Triangulating a drawable supergraph on the same vertex set and applying maximality isolates the extension argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
