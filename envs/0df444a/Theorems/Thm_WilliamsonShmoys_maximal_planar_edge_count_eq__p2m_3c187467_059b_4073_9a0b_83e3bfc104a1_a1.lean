-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:29.525875+00:00
-- url     : https://prove2.me/theorems/deff29d9-5a9a-4a55-a466-fc15c898aa4f
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
