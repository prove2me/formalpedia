-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_maximal_extension__p2m_dfeab8e7_c65a_497d_a20d_7cce49bd8d27_a2
-- name    : WilliamsonShmoys.finite_graph_maximal_extension__p2m_dfeab8e7_c65a_497d_a20d_7cce49bd8d27_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:45.815772+00:00
-- url     : https://prove2.me/theorems/b3aaf454-7ccc-4dcd-a4d6-d47dabe6d543
-- title:
--   Maximum-cardinality extension for a predicate on finite graphs
-- statement:
--   For any property of graphs on a finite vertex type, if H has that property, then H has a supergraph with the property whose edge count is maximal among such supergraphs. The hypothesis that H has the property makes the candidate family nonempty, including in boundary cases such as an empty vertex type. Finiteness of the graph family supplies a maximum; the parent obtains the target by taking P to be `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_graph_maximal_extension__p2m_dfeab8e7_c65a_497d_a20d_7cce49bd8d27_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hP : P H) : ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ ∀ L : SimpleGraph V, K ≤ L → P L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
