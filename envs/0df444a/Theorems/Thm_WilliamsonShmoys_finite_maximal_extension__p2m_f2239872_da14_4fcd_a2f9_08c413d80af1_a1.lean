-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_f2239872_da14_4fcd_a2f9_08c413d80af1_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_f2239872_da14_4fcd_a2f9_08c413d80af1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:15.99966+00:00
-- url     : https://prove2.me/theorems/fe6ffdb7-db07-4cee-9965-0cee09c3b00f
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property has a maximal supergraph satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.finite_maximal_extension__p2m_f2239872_da14_4fcd_a2f9_08c413d80af1_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H := by
  sorry
