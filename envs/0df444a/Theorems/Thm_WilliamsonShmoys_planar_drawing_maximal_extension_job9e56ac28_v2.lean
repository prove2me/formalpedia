-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_job9e56ac28_v2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_job9e56ac28_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:37:50.969948+00:00
-- url     : https://prove2.me/theorems/31870010-5062-46f4-994c-b103372bc022
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph is contained in a drawable graph on the same finite vertex type that has no drawable strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_job9e56ac28_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by sorry
