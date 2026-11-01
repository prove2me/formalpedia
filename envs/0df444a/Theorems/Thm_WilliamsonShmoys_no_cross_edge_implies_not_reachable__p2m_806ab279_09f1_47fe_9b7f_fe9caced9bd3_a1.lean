-- Prove2me | Theorems.Thm_WilliamsonShmoys_no_cross_edge_implies_not_reachable__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
-- name    : WilliamsonShmoys.no_cross_edge_implies_not_reachable__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:39.347694+00:00
-- url     : https://prove2.me/theorems/38a915d1-c3a6-4f7e-a576-04380bc2ddd9
-- title:
--   An edge-free cut separates reachability
-- statement:
--   If there are no graph edges from a set to its complement, then a vertex in the set cannot be reachable from a vertex in the complement. Prove this by induction on a walk and use the endpoint memberships to rule out a crossing edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.no_cross_edge_implies_not_reachable__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (A : Set V)
    (hno : ∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v)
    (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    ¬ G.Reachable u v := by sorry
