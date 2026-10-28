-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximum_edge_count_drawable_supergraph
-- name    : WilliamsonShmoys.exists_maximum_edge_count_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:22:47.377748+00:00
-- url     : https://prove2.me/theorems/22af61f1-7829-497b-862e-a496632ca6bc
-- title:
--   Drawable supergraph with maximum edge count
-- statement:
--   Among drawable supergraphs of a drawable graph on a finite vertex type, one has maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximum_edge_count_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ H' : SimpleGraph V,
        K ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' →
          H'.edgeSet.ncard ≤ H.edgeSet.ncard) := by sorry
