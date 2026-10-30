-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count_9367f2ac
-- name    : WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count_9367f2ac
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:37:14.123311+00:00
-- url     : https://prove2.me/theorems/80974a87-0e28-4da7-ad88-4d5a3af973bf
-- title:
--   Maximal drawable graphs satisfy the Euler edge count
-- statement:
--   A drawable simple graph on at least three vertices with no strict drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count_9367f2ac
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
