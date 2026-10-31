-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_5b94020c_9ee6_4950_8133_0664742e8f38_a2
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_5b94020c_9ee6_4950_8133_0664742e8f38_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:50.075181+00:00
-- url     : https://prove2.me/theorems/19ba793e-a642-460f-8ee0-bee7121a0e28
-- title:
--   Lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among its drawable supergraphs has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_5b94020c_9ee6_4950_8133_0664742e8f38_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
