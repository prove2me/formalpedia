-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:22:57.134154+00:00
-- url     : https://prove2.me/theorems/12627fe4-bb8b-4611-a4bf-2ba10834172b
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no strictly larger drawable simple supergraph has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
