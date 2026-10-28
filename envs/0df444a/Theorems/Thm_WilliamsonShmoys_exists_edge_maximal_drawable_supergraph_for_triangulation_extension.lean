-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph_for_triangulation_extension
-- name    : WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:24:56.283483+00:00
-- url     : https://prove2.me/theorems/0d5a79ab-6a7a-497b-8bde-7c8b8c4a8325
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on the same vertices. The family is nonempty because it contains the input graph, and finiteness of the possible simple graphs gives a maximal member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hYdraw : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V, Z ≤ W →
        WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z := by
  sorry
