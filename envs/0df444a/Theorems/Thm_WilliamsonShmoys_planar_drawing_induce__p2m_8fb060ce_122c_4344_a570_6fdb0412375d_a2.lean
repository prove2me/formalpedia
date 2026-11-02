-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- name    : WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:51:30.736847+00:00
-- url     : https://prove2.me/theorems/27b7dd3e-b559-4f79-a95b-58d9ac2af484
-- title:
--   Planar drawing restricts to induced subgraphs
-- statement:
--   Restricting the point map and edge curves of a drawing to a vertex subset gives a drawing of the induced graph. Injectivity, endpoint conditions, and nonintersection follow from the original drawing, while induced adjacency ensures every edge being drawn was an edge of the original graph. This is the geometric step needed for each large block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (s : Set V) :
    letI : Fintype {v // v ∈ s} := Fintype.ofFinite _
    HasPlanarDrawingOn (N.induce s) := by sorry
