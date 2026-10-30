-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_upper_bound_981f13e1
-- name    : WilliamsonShmoys.edge_upper_bound_981f13e1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:14:45.804429+00:00
-- url     : https://prove2.me/theorems/e54d2930-9aa2-40dd-90b4-f5fef531c453
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A finite simple graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices has at most 3|V|−6 edges. Prove this using Euler’s formula and face-boundary counting, treating disconnected drawings and isolated vertices explicitly. This removes the general planar upper-count obligation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_upper_bound_981f13e1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  sorry
