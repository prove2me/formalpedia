-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_graph_property_has_maximal_extension__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
-- name    : WilliamsonShmoys.finite_hereditary_graph_property_has_maximal_extension__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:09.816537+00:00
-- url     : https://prove2.me/theorems/ce32e0cf-9816-4c6d-abfc-f54c4b278919
-- title:
--   Finite maximal extension for hereditary graph properties
-- statement:
--   For a finite vertex type, every graph satisfying a property preserved under edge deletion is contained in a graph maximal among those satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_graph_property_has_maximal_extension__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
    {V : Type} [Fintype V]
    (N : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hN : P N)
    (hhered : ∀ {G H : SimpleGraph V}, H ≤ G → P G → P H) :
    ∃ K : SimpleGraph V, N ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by sorry
