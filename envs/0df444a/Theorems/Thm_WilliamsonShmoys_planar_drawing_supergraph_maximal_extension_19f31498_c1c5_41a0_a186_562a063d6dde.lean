-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde
-- name    : WilliamsonShmoys.planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:34:46.623976+00:00
-- url     : https://prove2.me/theorems/daa06fa8-84cb-4fa1-af0d-140debcb034f
-- title:
--   Maximal drawing-preserving supergraph extension
-- statement:
--   Every finite graph with a planar drawing has a planar-drawable supergraph on the same vertex set that is maximal under edge inclusion among planar-drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        J.edgeSet = H.edgeSet := by sorry
