-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_e4624ca0
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_e4624ca0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:15:55.720557+00:00
-- url     : https://prove2.me/theorems/88f9a966-3460-472e-b6cb-6754bcc5fbb9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges. This is the remaining topological graph theory obligation: establish that maximality forces a triangulation, and then derive the count from Euler’s formula and face-edge incidences. At three vertices, maximality gives K₃ and the same equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_e4624ca0
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, HasPlanarDrawingOn M → L ≤ M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
