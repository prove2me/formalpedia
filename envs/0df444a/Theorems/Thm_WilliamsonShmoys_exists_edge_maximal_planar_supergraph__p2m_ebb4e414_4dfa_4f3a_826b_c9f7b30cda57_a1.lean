-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:13.501179+00:00
-- url     : https://prove2.me/theorems/1f739e1d-0ba8-44b1-b52b-9de508987c2b
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that admits no strict drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        H ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        J = H := by sorry
