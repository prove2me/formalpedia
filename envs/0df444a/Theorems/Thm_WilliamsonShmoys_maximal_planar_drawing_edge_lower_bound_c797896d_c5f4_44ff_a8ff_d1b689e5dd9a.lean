-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:43:58.817707+00:00
-- url     : https://prove2.me/theorems/501982a3-cf58-468c-be32-1d2a30e3e83a
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
