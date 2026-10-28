-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_finite_vertex_graph
-- name    : WilliamsonShmoys.maximal_drawable_extension_finite_vertex_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:02:51.9819+00:00
-- url     : https://prove2.me/theorems/4c4c2d63-6f14-45e4-9dde-0337754a1861
-- title:
--   A drawable graph has an inclusion-maximal drawable extension on a finite vertex set
-- statement:
--   Every drawable graph on a finite vertex set has a drawable supergraph that is inclusion-maximal among drawable supergraphs on that same set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_extension_finite_vertex_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, G.edgeSet ⊆ W.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W.edgeSet ⊆ X.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn X → X.edgeSet ⊆ W.edgeSet := by sorry
