-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:54.117975+00:00
-- url     : https://prove2.me/theorems/9bc8f5f5-22dd-4255-9d37-0a6f5ce9c2a7
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A graph maximal among planar graphs on the same vertex type, with at least three vertices, has at least 3V − 6 edges, expressed as 3V ≤ E + 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  sorry
