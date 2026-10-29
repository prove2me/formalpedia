-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:57:42.771856+00:00
-- url     : https://prove2.me/theorems/e1448a29-6ed5-4290-9f2f-9b3459d52881
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   For any finite drawable graph, there is a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V,
        (∀ u v, S.Adj u v → T.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn T →
        ∀ u v, T.Adj u v → S.Adj u v := by sorry
