-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424
-- name    : WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:40:23.59151+00:00
-- url     : https://prove2.me/theorems/9b1de031-9f3a-4b12-85af-57ed9adde3d2
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most three times its vertex count minus six edges, expressed without natural-number subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
