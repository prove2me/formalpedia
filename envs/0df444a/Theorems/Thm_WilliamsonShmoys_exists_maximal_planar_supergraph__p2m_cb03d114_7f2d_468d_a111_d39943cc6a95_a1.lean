-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:28:58.646968+00:00
-- url     : https://prove2.me/theorems/20ba4ff1-cfc3-485c-a806-05ed9b53c7fa
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on this finite vertex type has a drawable supergraph that has no strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ P : SimpleGraph V,
        (∀ u v, N.Adj u v → P.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        ∀ u v, P.Adj u v → N.Adj u v) := by sorry
