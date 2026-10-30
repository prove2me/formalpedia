-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_euler_face_incidence
-- name    : WilliamsonShmoys.planar_graph_euler_face_incidence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:14:08.159236+00:00
-- url     : https://prove2.me/theorems/e9ef2b10-8ddc-4b14-8636-269173947867
-- title:
--   Face incidence bound for an Euler face count
-- statement:
--   For a connected graph on at least three vertices with a drawing satisfying HasPlanarDrawingOn, any natural number F satisfying the Euler face-count equation has at least three edge incidences per face in aggregate: 3F ≤ 2|E|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.planar_graph_euler_face_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (F : ℕ)
    (hEuler : Fintype.card V + F = Y.edgeSet.ncard + 2) :
    3 * F ≤ 2 * Y.edgeSet.ncard := by sorry
