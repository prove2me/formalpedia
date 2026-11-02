-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a3
-- name    : WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:15:33.033283+00:00
-- url     : https://prove2.me/theorems/d3634604-6d84-4b01-a257-7ac1759b320a
-- title:
--   Edge bound from triangulation data
-- statement:
--   Combine the edge-count inequality with the Euler and triangular-face equations to derive the target bound. This child removes only the arithmetic from the parent; it is independently provable by `omega`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (f : Nat)
    (hsub : ∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v)
    (hle : H.edgeFinset.card ≤ K.edgeFinset.card)
    (heuler : K.edgeFinset.card + 2 = Fintype.card V + f)
    (hfaces : 3 * f = 2 * K.edgeFinset.card) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  sorry
