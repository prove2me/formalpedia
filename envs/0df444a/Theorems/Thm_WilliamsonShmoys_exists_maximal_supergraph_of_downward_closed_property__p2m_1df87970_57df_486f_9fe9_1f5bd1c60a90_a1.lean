-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed_property__p2m_1df87970_57df_486f_9fe9_1f5bd1c60a90_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed_property__p2m_1df87970_57df_486f_9fe9_1f5bd1c60a90_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:38.704247+00:00
-- url     : https://prove2.me/theorems/d9db2d96-cb27-4a78-8ca4-1c2a63350887
-- title:
--   Finite maximality for a downward-closed graph property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property has a supergraph that is maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed_property__p2m_1df87970_57df_486f_9fe9_1f5bd1c60a90_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hdown : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧ P J ∧
      ∀ K : SimpleGraph V, J ≤ K → P K → K = J := by sorry
