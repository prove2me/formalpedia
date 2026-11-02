-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite__p2m_89fd7ec5_d704_44ae_9887_a6594412388a_a3
-- name    : WilliamsonShmoys.exists_maximal_extension_finite__p2m_89fd7ec5_d704_44ae_9887_a6594412388a_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:32.052795+00:00
-- url     : https://prove2.me/theorems/1e33cd4f-d8fc-4ec3-ac99-8e5e2babb00f
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, a graph satisfying the property has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_finite__p2m_89fd7ec5_d704_44ae_9887_a6594412388a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V -> Prop)
    (K : SimpleGraph V)
    (hK : P K) :
    Exists fun H : SimpleGraph V => And (LE.le K H)
      (And (P H) (∀ J : SimpleGraph V, LE.le H J -> P J -> LE.le J H)) := by
  sorry
