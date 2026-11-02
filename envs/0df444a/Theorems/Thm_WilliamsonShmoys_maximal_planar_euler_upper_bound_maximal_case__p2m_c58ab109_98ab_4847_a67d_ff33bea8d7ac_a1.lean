-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_upper_bound_maximal_case__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
-- name    : WilliamsonShmoys_maximal_planar_euler_upper_bound_maximal_case__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:03:59.994204+00:00
-- url     : https://prove2.me/theorems/e4fb4528-3000-447a-a91c-bbceedbe6374
-- title:
--   Euler bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal simple graph admitting the stated crossing-free drawing has at most three times its number of vertices minus six edges, when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_euler_upper_bound_maximal_case__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
