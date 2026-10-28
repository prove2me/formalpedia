-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_for_face_accounting_57972424
-- name    : WilliamsonShmoys.planar_drawing_euler_for_face_accounting_57972424
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:35:16.402775+00:00
-- url     : https://prove2.me/theorems/0493c70a-93f5-4bdc-a172-424dbccb2680
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with a drawing satisfying HasPlanarDrawingOn has a face count satisfying Euler’s vertex-edge-face equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_euler_for_face_accounting_57972424
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    Exists (fun f : Nat => Fintype.card V + f = G.edgeSet.ncard + 2) := by sorry
