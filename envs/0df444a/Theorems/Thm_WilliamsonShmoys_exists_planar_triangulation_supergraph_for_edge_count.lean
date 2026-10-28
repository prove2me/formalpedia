-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_for_edge_count
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph_for_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:35:29.773595+00:00
-- url     : https://prove2.me/theorems/53742bd7-aa23-46f0-9a1d-8d4de61184b3
-- title:
--   Planar triangulation extension with edge count
-- statement:
--   Every connected drawable simple graph on a finite ordered vertex set of size at least three has a drawable supergraph on the same vertex set with exactly 3n−6 edges. This packages the planar triangulation extension and Euler-counting argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  sorry
