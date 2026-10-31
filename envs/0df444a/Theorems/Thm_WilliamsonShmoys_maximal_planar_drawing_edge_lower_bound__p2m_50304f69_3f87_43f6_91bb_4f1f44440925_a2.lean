-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:12:22.65284+00:00
-- url     : https://prove2.me/theorems/76d78def-4fcc-4b45-b88b-61d6f8602e64
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   A graph with the specified drawing that is maximal among drawable supergraphs on the same vertices and has at least three vertices has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) (hMax : forall T : SimpleGraph V, S <= T -> HasPlanarDrawingOn T -> T = S) : 3 * Fintype.card V - 6 <= S.edgeSet.ncard := by sorry
