-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:46:32.955247+00:00
-- url     : https://prove2.me/theorems/b56eab82-262a-40b0-bbe5-afbad2b0b62f
-- title:
--   Maximal extension in a finite graph lattice
-- statement:
--   For a finite vertex type, any downward-closed graph property that holds of R has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hmono : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  sorry
