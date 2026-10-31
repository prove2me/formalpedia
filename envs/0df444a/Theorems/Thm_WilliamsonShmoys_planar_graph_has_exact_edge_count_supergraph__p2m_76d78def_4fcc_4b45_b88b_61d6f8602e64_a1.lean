-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_count_supergraph__p2m_76d78def_4fcc_4b45_b88b_61d6f8602e64_a1
-- name    : WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph__p2m_76d78def_4fcc_4b45_b88b_61d6f8602e64_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:33.899985+00:00
-- url     : https://prove2.me/theorems/49d536b5-943b-4c07-ac34-73c598814091
-- title:
--   Drawable planar graph completion with exact maximal edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3n−6 edges. This removes the parent’s maximality premise and supplies a canonical edge count for a drawable completion. A proof route is to connect components without crossings, triangulate the faces by adding edges, then apply Euler’s formula and count face-edge incidences. The case n=3 yields the triangle; disconnected inputs are included and must be connected during the completion argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph__p2m_76d78def_4fcc_4b45_b88b_61d6f8602e64_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) : ∃ T : SimpleGraph V, S <= T ∧ HasPlanarDrawingOn T ∧ 3 * Fintype.card V - 6 = T.edgeSet.ncard := by sorry
