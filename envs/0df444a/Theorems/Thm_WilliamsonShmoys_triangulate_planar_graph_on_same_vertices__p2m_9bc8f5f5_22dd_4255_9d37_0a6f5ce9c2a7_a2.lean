-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulate_planar_graph_on_same_vertices__p2m_9bc8f5f5_22dd_4255_9d37_0a6f5ce9c2a7_a2
-- name    : WilliamsonShmoys.triangulate_planar_graph_on_same_vertices__p2m_9bc8f5f5_22dd_4255_9d37_0a6f5ce9c2a7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:07.631204+00:00
-- url     : https://prove2.me/theorems/54b85171-3c84-49d0-b75e-a1ac45808ba4
-- title:
--   Triangulate a planar graph on the same vertex set
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex set of size at least three has a planar supergraph on that same vertex set with exactly 3|V| − 6 edges. This packages the maximal planar extension and Euler-count argument used by the target proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulate_planar_graph_on_same_vertices__p2m_9bc8f5f5_22dd_4255_9d37_0a6f5ce9c2a7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M ≤ N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
