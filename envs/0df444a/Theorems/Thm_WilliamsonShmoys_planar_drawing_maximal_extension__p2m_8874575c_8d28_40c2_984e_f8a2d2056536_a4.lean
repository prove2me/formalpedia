-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:51.688992+00:00
-- url     : https://prove2.me/theorems/624a938d-c9e5-41fb-88c5-28ffcc896cfe
-- title:
--   Extend a finite planar drawing to a maximal drawable graph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal under graph inclusion among drawable supergraphs. Since there are finitely many simple graphs on the vertex type, maximize the edge count among those containing the given graph and admitting a drawing; a proper drawable extension would have strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ T : SimpleGraph V, H ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
