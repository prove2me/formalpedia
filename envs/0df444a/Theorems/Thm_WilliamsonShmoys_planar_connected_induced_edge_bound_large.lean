-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_induced_edge_bound_large
-- name    : WilliamsonShmoys.planar_connected_induced_edge_bound_large
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:37:39.883033+00:00
-- url     : https://prove2.me/theorems/168c37d2-a1cd-4257-829e-99eabc1ea57a
-- title:
--   Connected planar induced graph Euler edge bound
-- statement:
--   A connected induced graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. This isolates the Euler and face-incidence argument; deriving the embedding facts and incidence counts remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_induced_edge_bound_large
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V)
    (hConnected : (H.induce (↑S : Set V)).Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn
      (H.induce (↑S : Set V)))
    (hLarge : 3 ≤ S.card) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ 3 * S.card - 6 := by sorry
