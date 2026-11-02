-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
-- name    : WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:07:50.696311+00:00
-- url     : https://prove2.me/theorems/f06b387f-0617-47ad-973b-8431b4044bd1
-- title:
--   Edge bound from triangulation data
-- statement:
--   Derive the target bound from the edge-count inequality and the Euler and face-incidence equations. This removes the arithmetic from the parent; a concrete proof route is `omega` over the natural-number equations. The hypotheses preserve the certificate supplied by the first child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 <= Fintype.card V)
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (f : Nat)
    (hsub : ∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v)
    (hle : H.edgeFinset.card ≤ K.edgeFinset.card)
    (heuler : K.edgeFinset.card + 2 = Fintype.card V + f)
    (hfaces : 3 * f = 2 * K.edgeFinset.card) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  sorry
