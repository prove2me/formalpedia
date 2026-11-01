-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:49.895621+00:00
-- url     : https://prove2.me/theorems/3576d770-ffd3-4c46-93e6-ddf44c5e528d
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
