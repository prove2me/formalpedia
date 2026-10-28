-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_for_maximal_edge_bound_50a3c5c3
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_for_maximal_edge_bound_50a3c5c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:14:33.500669+00:00
-- url     : https://prove2.me/theorems/64e1a493-6709-43d0-ad5c-0f58c94c4f53
-- title:
--   Extend a drawable graph to a triangulation on the same vertices
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension_for_maximal_edge_bound_50a3c5c3
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
