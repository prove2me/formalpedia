-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:06.370734+00:00
-- url     : https://prove2.me/theorems/5b94020c-9ee6-4950-8133-0664742e8f38
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable simple-graph supergraph has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
