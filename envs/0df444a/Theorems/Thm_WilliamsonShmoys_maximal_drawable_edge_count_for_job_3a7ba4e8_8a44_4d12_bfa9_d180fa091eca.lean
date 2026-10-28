-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_job_3a7ba4e8_8a44_4d12_bfa9_d180fa091eca
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_for_job_3a7ba4e8_8a44_4d12_bfa9_d180fa091eca
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:04:51.301614+00:00
-- url     : https://prove2.me/theorems/8a971d4a-2c9c-4fb3-9b34-1e8f0b46a217
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that has no proper drawable supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_for_job_3a7ba4e8_8a44_4d12_bfa9_d180fa091eca
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
