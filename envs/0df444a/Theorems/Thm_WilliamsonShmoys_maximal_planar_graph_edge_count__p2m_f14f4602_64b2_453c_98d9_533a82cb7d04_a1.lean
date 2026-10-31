-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:38.948718+00:00
-- url     : https://prove2.me/theorems/29d426c4-6f5c-451a-abaf-84dc0cba9aeb
-- title:
--   An edge-maximal planar graph with at least three vertices has 3n−6 edges
-- statement:
--   For a graph on a finite linearly ordered vertex type with at least three vertices, a drawing witness and edge-maximality among planar supergraphs imply the exact edge count 3|V|−6. The size boundary is necessary for this formula; the child preserves it explicitly. This removes the edge-count step from the parent. A proof route is to derive a plane embedding from the drawing, use maximality to show every face is triangular, and combine Euler's formula with the fact that each edge is incident to two face sides. The remaining obligation is to formalize those embedding, face, and counting arguments for the given arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 = H.edgeSet.ncard := by sorry
