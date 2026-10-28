-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_24bcd821_2a94_4cb2_b06f_eb5106ed464b
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_24bcd821_2a94_4cb2_b06f_eb5106ed464b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:47:15.917865+00:00
-- url     : https://prove2.me/theorems/13233146-3350-4c17-a758-20fc2bd70a47
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph on a linearly ordered vertex type with at least three vertices extends on the same type to a drawable graph with no drawable strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_24bcd821_2a94_4cb2_b06f_eb5106ed464b
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊂ N.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
