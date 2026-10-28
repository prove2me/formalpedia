-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_edge_count_lower_bound_ws
-- name    : WilliamsonShmoys.maximal_planar_simple_edge_count_lower_bound_ws
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:57:01.194775+00:00
-- url     : https://prove2.me/theorems/af94bdb0-79f9-44a2-8a31-4f1eea5ccf5e
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least three times its number of vertices minus six edges, written using addition to avoid truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_simple_edge_count_lower_bound_ws
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
