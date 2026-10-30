-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:45:47.722363+00:00
-- url     : https://prove2.me/theorems/5b678f02-c398-4f79-9d5b-0f91515c17ad
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
