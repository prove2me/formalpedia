-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:13:55.319986+00:00
-- url     : https://prove2.me/theorems/4395d72b-f64b-4a4d-8463-8f3f8fcb21e0
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   An edge-maximal simple planar graph on at least three vertices has at least 3n−6 edges, by the Euler face-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M.edgeSet ≤ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet = M.edgeSet) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
