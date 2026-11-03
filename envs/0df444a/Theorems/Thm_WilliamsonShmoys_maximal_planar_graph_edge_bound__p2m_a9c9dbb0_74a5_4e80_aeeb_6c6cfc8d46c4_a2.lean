-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:23.551561+00:00
-- url     : https://prove2.me/theorems/e364c09d-03b7-4604-b246-80ad4b3eeeb7
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   For at least three vertices, a drawable graph maximal among drawable supergraphs on the same vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : (letI : DecidableRel H.Adj := Classical.decRel H.Adj; H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
