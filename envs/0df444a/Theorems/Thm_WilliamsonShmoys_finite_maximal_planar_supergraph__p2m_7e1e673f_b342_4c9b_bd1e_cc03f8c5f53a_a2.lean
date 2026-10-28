-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:31:51.965227+00:00
-- url     : https://prove2.me/theorems/2d2efbeb-7ceb-4fa3-8371-f356ba71853f
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   Every finite drawable graph is contained in an inclusion-maximal drawable graph on the same vertex set. Prove this by maximizing edge count among the finite collection of drawable supergraphs; the maximality condition says every drawable supergraph of R is equal to R.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_7e1e673f_b342_4c9b_bd1e_cc03f8c5f53a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      (∀ S : SimpleGraph V,
        (∀ u v, T.Adj u v → S.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn S →
        (∀ u v, R.Adj u v → S.Adj u v) → S = R) ∧
      WilliamsonShmoys.HasPlanarDrawingOn R := by sorry
