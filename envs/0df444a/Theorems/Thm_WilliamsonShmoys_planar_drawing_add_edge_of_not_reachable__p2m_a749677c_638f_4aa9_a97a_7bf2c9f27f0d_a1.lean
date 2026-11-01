-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_not_reachable__p2m_a749677c_638f_4aa9_a97a_7bf2c9f27f0d_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_of_not_reachable__p2m_a749677c_638f_4aa9_a97a_7bf2c9f27f0d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:14.793047+00:00
-- url     : https://prove2.me/theorems/bb5f5d4f-392b-4f4a-9b52-6b3fedbce8c7
-- title:
--   Add a drawable edge between distinct connected components
-- statement:
--   Given a drawable graph and two vertices in distinct connected components, add an edge while preserving drawability. The parent obtains the separation premise from its edge-free partition; this child isolates the reusable geometric construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_of_not_reachable__p2m_a749677c_638f_4aa9_a97a_7bf2c9f27f0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (u v : V)
    (hsep : ¬ M.Reachable u v)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by sorry
