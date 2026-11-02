-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:11:53.980521+00:00
-- url     : https://prove2.me/theorems/3f244f53-8936-4715-8547-0063dd70ff12
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        K ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H ≤ J → J = H := by
  sorry
