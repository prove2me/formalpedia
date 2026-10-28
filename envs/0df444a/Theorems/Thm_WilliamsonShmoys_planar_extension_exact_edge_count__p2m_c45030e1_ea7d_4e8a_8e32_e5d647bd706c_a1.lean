-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_exact_edge_count__p2m_c45030e1_ea7d_4e8a_8e32_e5d647bd706c_a1
-- name    : WilliamsonShmoys.planar_extension_exact_edge_count__p2m_c45030e1_ea7d_4e8a_8e32_e5d647bd706c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:52:51.514997+00:00
-- url     : https://prove2.me/theorems/aaf88115-3b68-495f-bd0f-37f00b1cdc73
-- title:
--   Planar graphs extend to a triangulation on the same vertices
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing can be extended, using the same vertices, to a crossing-free triangulation with exactly 3|V| - 6 edges. The three-vertex boundary case yields the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_exact_edge_count__p2m_c45030e1_ea7d_4e8a_8e32_e5d647bd706c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G <= M ∧ HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
