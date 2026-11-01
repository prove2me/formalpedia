-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:21.691255+00:00
-- url     : https://prove2.me/theorems/e768399d-d885-4104-a7d5-24e1472f84ce
-- title:
--   Every drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   On a fixed finite vertex type, every drawable graph is contained in a drawable graph that has no strictly larger drawable supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
