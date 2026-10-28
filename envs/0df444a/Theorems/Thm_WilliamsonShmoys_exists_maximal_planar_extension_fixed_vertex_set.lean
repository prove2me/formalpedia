-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_fixed_vertex_set
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_fixed_vertex_set
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:02:23.351542+00:00
-- url     : https://prove2.me/theorems/d3dc1977-f889-4b97-b836-ea53a7432738
-- title:
--   Maximal drawable extension on a fixed vertex set
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs by edge inclusion. The candidates form a finite nonempty set: there are finitely many simple graphs on the vertex type, and the original graph is a candidate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_fixed_vertex_set
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by sorry
