-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_9f4db670
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_9f4db670
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:43:40.766247+00:00
-- url     : https://prove2.me/theorems/c1bde5d0-81f8-47d3-8ae4-528ec5fce967
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same type with no drawable strict supergraph. This removes the finite maximality choice from the parent. Prove it by maximizing edge count among the finitely many supergraphs containing `G` that satisfy the drawing predicate. The child does not require a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_9f4db670
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      G.edgeSet ⊆ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L.edgeSet ⊂ K.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
