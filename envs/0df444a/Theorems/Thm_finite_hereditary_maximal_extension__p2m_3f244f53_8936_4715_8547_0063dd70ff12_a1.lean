-- Prove2me | Theorems.Thm_finite_hereditary_maximal_extension__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
-- name    : finite_hereditary_maximal_extension__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:23:52.37492+00:00
-- url     : https://prove2.me/theorems/b6ae21db-893f-4c4f-a026-a39601d60fc0
-- title:
--   Maximal extension for a hereditary property on a finite graph type
-- statement:
--   If a property of simple graphs on a finite vertex type is inherited by subgraphs, every graph satisfying it has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_hereditary_maximal_extension__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, K ≤ J → P J → H ≤ J → J = H := by
  sorry
