-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_monotone_property_has_maximal_supergraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
-- name    : WilliamsonShmoys.finite_monotone_property_has_maximal_supergraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:08.213485+00:00
-- url     : https://prove2.me/theorems/b3c7eed8-a281-43e0-bad6-9aee20a9edf2
-- title:
--   Finite graphs have maximal supergraphs for downward-closed properties
-- statement:
--   For a finite vertex type, any graph satisfying a property inherited by subgraphs has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_monotone_property_has_maximal_supergraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V → Prop)
    (hmono : ∀ {G H : SimpleGraph V}, G ≤ H → Q H → Q G)
    (K : SimpleGraph V) (hK : Q K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ Q H ∧
      ∀ H' : SimpleGraph V, H ≤ H' → Q H' → H' = H := by
  sorry
