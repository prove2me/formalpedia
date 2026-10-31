-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- name    : WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:22.475978+00:00
-- url     : https://prove2.me/theorems/aa360b7d-83e7-4a10-9952-960bd13962a8
-- title:
--   A maximal drawable graph with at least three vertices is connected
-- statement:
--   An inclusion-maximal drawable graph with at least three vertices is connected. If it were disconnected, use the given drawing to choose vertices in distinct components and extend the drawing by an arc joining them, producing a drawable strict supergraph. The lower bound on the vertex count is retained as in the parent. This isolates the geometric work: prove the arc extension satisfies continuity, injectivity, avoidance of vertex positions in its interior, and the noncrossing conditions for all edges. The route uses a face of the finite plane embedding incident to distinct components and a connecting arc within that face; this is the main remaining obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L) : L.Connected := by sorry
