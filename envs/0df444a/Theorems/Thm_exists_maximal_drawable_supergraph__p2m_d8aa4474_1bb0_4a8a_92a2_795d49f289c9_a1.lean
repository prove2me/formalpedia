-- Prove2me | Theorems.Thm_exists_maximal_drawable_supergraph__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- name    : exists_maximal_drawable_supergraph__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:13.448774+00:00
-- url     : https://prove2.me/theorems/06511e8e-1279-4bc2-b7ef-97610e0642c8
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal under subgraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem exists_maximal_drawable_supergraph__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ K ≤ M ∧
        ∀ J : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn J → M ≤ J → J ≤ M := by
  sorry
