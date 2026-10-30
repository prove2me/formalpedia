-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_bound_20261026
-- name    : WilliamsonShmoys.maximal_drawable_extension_edge_bound_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:44:50.003879+00:00
-- url     : https://prove2.me/theorems/69ce0ef3-265b-4736-9586-9fa66806d552
-- title:
--   Euler edge bound for a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges, including the boundary case |V|=3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_extension_edge_bound_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
