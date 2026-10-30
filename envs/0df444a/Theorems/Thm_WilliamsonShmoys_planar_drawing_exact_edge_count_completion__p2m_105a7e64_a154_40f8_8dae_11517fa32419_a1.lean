-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:37.367471+00:00
-- url     : https://prove2.me/theorems/45b06a26-f6d7-4266-b401-312835dd7478
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_105a7e64_a154_40f8_8dae_11517fa32419_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
