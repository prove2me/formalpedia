-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_certificate_monotone_edge_bound__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- name    : WilliamsonShmoys.euler_certificate_monotone_edge_bound__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:09:01.834665+00:00
-- url     : https://prove2.me/theorems/49cc73c5-21b3-4c10-babc-23d7c77fbe7b
-- title:
--   Euler certificate implies the planar edge bound
-- statement:
--   Transfer the Euler certificate’s edge bound from a graph H to its subgraph G. Unpack the certificate, combine `n + f = m + 2` with `3f ≤ 2m` to obtain `m + 6 ≤ 3n`, then use monotonicity of finite edge-set cardinality under `G ≤ H`. This removes all topological work from the parent and leaves only graph-set monotonicity and natural-number arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_certificate_monotone_edge_bound__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hCard : 3 ≤ Fintype.card V)
    (hcert : ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
