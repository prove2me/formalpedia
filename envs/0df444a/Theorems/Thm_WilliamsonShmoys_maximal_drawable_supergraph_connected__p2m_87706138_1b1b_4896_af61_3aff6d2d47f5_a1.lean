-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_connected__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_connected__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:47.428527+00:00
-- url     : https://prove2.me/theorems/638cd013-f422-4f43-912d-3f97f91e2a69
-- title:
--   A maximal drawable supergraph is connected
-- statement:
--   If a drawable simple graph on at least three vertices has no strictly larger drawable supergraph on the same vertex set, then it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_supergraph_connected__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.Connected := by sorry
