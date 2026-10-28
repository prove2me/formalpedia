-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_8a5c5037_77da_430d_9643_dec01e9a1ed1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_8a5c5037_77da_430d_9643_dec01e9a1ed1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:10:34.437206+00:00
-- url     : https://prove2.me/theorems/e47c1740-7cba-4f95-a8bb-b2d562eb8f0b
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is inclusion-maximal among drawable supergraphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_8a5c5037_77da_430d_9643_dec01e9a1ed1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet := by sorry
