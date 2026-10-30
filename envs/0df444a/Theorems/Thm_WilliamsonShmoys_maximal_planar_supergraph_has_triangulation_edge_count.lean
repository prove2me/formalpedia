-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_planar_supergraph_has_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:07:30.635998+00:00
-- url     : https://prove2.me/theorems/c04c4e3a-661a-4f0e-8177-08736887fdcf
-- title:
--   A maximum planar supergraph has the triangulation edge count
-- statement:
--   A planar supergraph with maximum edge count among planar supergraphs of a fixed planar graph has exactly 3|V|−6 edges when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_has_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (K : SimpleGraph V)
    (hNK : N ≤ K)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, N ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
