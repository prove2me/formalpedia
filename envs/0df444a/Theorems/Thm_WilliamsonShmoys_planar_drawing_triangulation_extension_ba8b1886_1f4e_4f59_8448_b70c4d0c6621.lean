-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_ba8b1886_1f4e_4f59_8448_b70c4d0c6621
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_ba8b1886_1f4e_4f59_8448_b70c4d0c6621
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:58:22.832966+00:00
-- url     : https://prove2.me/theorems/19f31498-c1c5-41a0-a186-562a063d6dde
-- title:
--   Extend a finite planar drawing to a triangulated planar graph
-- statement:
--   Any finite simple graph on at least three vertices with a crossing-free drawing is a subgraph of a simple graph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_ba8b1886_1f4e_4f59_8448_b70c4d0c6621
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
