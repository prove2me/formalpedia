-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:56.106011+00:00
-- url     : https://prove2.me/theorems/50a29994-a325-484b-b52e-c568c6fdc691
-- title:
--   Edge count of a maximal finite planar graph
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable supergraph on the same vertex type has exactly `3|V| − 6` edges. The proof route is to show maximality forces triangular faces, then use Euler’s formula and count face-edge incidences. The `3 ≤ Fintype.card V` hypothesis covers the boundary case of three vertices and is retained for the planar edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hMax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
