-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:40.308033+00:00
-- url     : https://prove2.me/theorems/ce111785-bfc4-489c-a8dc-4146b3253516
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   On a finite ordered vertex type with at least three vertices, an inclusion-maximal graph admitting the specified crossing-free drawing has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
