-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a1
-- name    : WilliamsonShmoys.maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:22.379615+00:00
-- url     : https://prove2.me/theorems/32ba3740-8177-4bb4-84ec-10f63a64f0d3
-- title:
--   Face counts for a maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices that is maximal among graphs admitting the specified crossing-free drawing has a face count satisfying Euler’s equation and the triangular face-incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, T ≤ N → HasPlanarDrawingOn N → N ≤ T) : ∃ f : ℕ, Fintype.card V + f = T.edgeSet.ncard + 2 ∧ 3 * f = 2 * T.edgeSet.ncard := by sorry
