-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_ecade84c_ffb2_4aac_a689_428692de6887_a1
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_ecade84c_ffb2_4aac_a689_428692de6887_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:26.476665+00:00
-- url     : https://prove2.me/theorems/98915fb2-fad3-4066-b195-28760c9e8707
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly 3 times the number of vertices minus 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_ecade84c_ffb2_4aac_a689_428692de6887_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       3 * Fintype.card V = R.edgeFinset.card + 6) := by sorry
