-- Prove2me | Theorems.Thm_WilliamsonShmoys_has_edge_maximal_planar_completion__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- name    : WilliamsonShmoys.has_edge_maximal_planar_completion__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:15:04.303589+00:00
-- url     : https://prove2.me/theorems/a6c79c1c-4522-4952-80c8-2c98cd425351
-- title:
--   Finite edge-maximal drawable completion
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that has no drawable strict supergraph. The strictness condition ensures this expresses edge-maximality, not just inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.has_edge_maximal_planar_completion__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
