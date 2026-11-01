-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- name    : WilliamsonShmoys.simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:47.9102+00:00
-- url     : https://prove2.me/theorems/22003a04-aff0-4d5b-b1d3-902c88d5c97f
-- title:
--   Simple planar graph edge bound
-- statement:
--   A simple connected graph with the specified planar drawing and at least three vertices has at most three times its vertex count minus six edges, expressed without natural-number subtraction. The size hypothesis retains the boundary condition needed for the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
