-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T11:59:24.617208+00:00
-- url     : https://prove2.me/theorems/ade061e0-083b-4a3b-882e-6784f9579cdf
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly three times the number of vertices minus six edges. The three-vertex boundary case completes to the triangle. For larger vertex sets, the proof route is planar completion to a maximal drawing, triangulation, and Euler counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
