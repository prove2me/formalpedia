-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_for_extension_561cc06e
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal_for_extension_561cc06e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:15:37.296116+00:00
-- url     : https://prove2.me/theorems/6cf77740-43ef-4590-9f42-077558e160f4
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no drawable strict supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal_for_extension_561cc06e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V =>
      And (Set.Subset K.edgeSet L.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn L)
          (∀ M : SimpleGraph V,
            WilliamsonShmoys.HasPlanarDrawingOn M →
            Set.Subset L.edgeSet M.edgeSet →
            L.edgeSet = M.edgeSet)) := by sorry
