-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:25.489598+00:00
-- url     : https://prove2.me/theorems/05a50faf-c208-4b89-a21d-3d6ee49fb52f
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   A maximal simple graph with a crossing-free drawing on at least three vertices has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      G ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = G) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by sorry
