-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_extends_to_triangulation__p2m_f90853da_a441_4590_8374_63300059b95b_a1
-- name    : WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_f90853da_a441_4590_8374_63300059b95b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:59.971075+00:00
-- url     : https://prove2.me/theorems/f14f4602-64b2-453c-98d9-533a82cb7d04
-- title:
--   Extend a planar graph to a triangulation on the same vertices
-- statement:
--   Any graph with a crossing-free drawing on at least three vertices is a subgraph of a triangulated planar graph on the same vertex set, whose edge count is exactly three times the vertex count minus six. The claim includes disconnected graphs and graphs with isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_f90853da_a441_4590_8374_63300059b95b_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ 3 * Fintype.card V - 6 = H.edgeSet.ncard := by sorry
