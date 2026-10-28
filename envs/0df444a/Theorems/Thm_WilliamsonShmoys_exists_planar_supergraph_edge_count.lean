-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_count
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:56:11.300065+00:00
-- url     : https://prove2.me/theorems/3a7ba4e8-8a44-4d12-bfa9-d180fa091eca
-- title:
--   Drawable supergraph with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable supergraph on that same vertex type with exactly 3|V|−6 edges. The parent uses this witness and its maximality hypothesis to identify the supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
