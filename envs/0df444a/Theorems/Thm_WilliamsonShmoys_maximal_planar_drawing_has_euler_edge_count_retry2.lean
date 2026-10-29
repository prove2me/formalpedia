-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count_retry2
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:05:50.751993+00:00
-- url     : https://prove2.me/theorems/45cc48cb-2419-43df-b4b6-ff2643ac8c59
-- title:
--   Edge count of a saturated planar drawing
-- statement:
--   A finite simple graph on at least three vertices whose crossing-free drawing cannot be extended by adding edges has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hSat : ∀ M : SimpleGraph V, L <= M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M <= L) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
