-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_1e3a6908_3e59_4565_92f0_171f972a39c8_a2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_1e3a6908_3e59_4565_92f0_171f972a39c8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:22.531975+00:00
-- url     : https://prove2.me/theorems/3f9c3645-d252-4a90-a181-e1c18a19d87d
-- title:
--   Finite simple graphs admit maximal predicate supergraphs
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, if H satisfies the predicate, then H has a predicate-satisfying supergraph maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_1e3a6908_3e59_4565_92f0_171f972a39c8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ K' : SimpleGraph V, K ≤ K' → P K' → K' = K := by sorry
