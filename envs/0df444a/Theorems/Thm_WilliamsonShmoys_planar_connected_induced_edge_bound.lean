-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_induced_edge_bound
-- name    : WilliamsonShmoys.planar_connected_induced_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:29:16.888043+00:00
-- url     : https://prove2.me/theorems/4564d1ad-4947-455c-8130-1489c14a5ca6
-- title:
--   Edge bound for a connected planar induced subgraph
-- statement:
--   For a nonempty vertex subset whose induced graph is connected and has a crossing-free drawing, its edge count is at most half its vertex count for sizes below three, and at most three times its vertex count minus six otherwise. The small cases follow from simplicity; the larger case follows from Euler’s formula and face-boundary incidence counting. This removes the geometric edge-count argument from the parent theorem, leaving only its pointwise application to each partition member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_induced_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V)
    (hNonempty : S.Nonempty)
    (hConnected : (H.induce (↑S : Set V)).Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn
      (H.induce (↑S : Set V))) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤
      (if S.card < 3 then S.card / 2 else 3 * S.card - 6) := by sorry
