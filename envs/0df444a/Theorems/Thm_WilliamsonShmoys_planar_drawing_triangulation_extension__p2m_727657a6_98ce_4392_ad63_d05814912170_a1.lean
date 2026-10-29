-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_727657a6_98ce_4392_ad63_d05814912170_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_727657a6_98ce_4392_ad63_d05814912170_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T23:20:30.818567+00:00
-- url     : https://prove2.me/theorems/4374e3c1-5003-44b4-a318-b760ef8ecee9
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges. This is the triangulation extension step needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_727657a6_98ce_4392_ad63_d05814912170_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hDraw : HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧
      Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
