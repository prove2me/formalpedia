-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:45.561394+00:00
-- url     : https://prove2.me/theorems/650425a5-d9a9-49da-be57-f1af1f6688f7
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
