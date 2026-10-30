-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_upper_bound_connected
-- name    : WilliamsonShmoys.edge_upper_bound_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:29:47.528184+00:00
-- url     : https://prove2.me/theorems/b2651101-1aa0-4db8-8c6b-e2983a7a8cb2
-- title:
--   Planar edge bound for connected drawings
-- statement:
--   A finite connected simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3|V|−6` edges. This is the main topological obligation; it must be proved from the supplied drawing rather than assumed from a generic face-bound theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_upper_bound_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConn : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  sorry
