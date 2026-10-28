-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound_e2343c2d
-- name    : WilliamsonShmoys.maximal_drawable_edge_bound_e2343c2d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:09:55.345855+00:00
-- url     : https://prove2.me/theorems/5a5a6565-c1b1-4c52-8ac2-d3ae49e455ef
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable supergraph on those vertices has at least `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_bound_e2343c2d
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → K ≠ N → ¬ HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
