-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
-- name    : WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:54.61519+00:00
-- url     : https://prove2.me/theorems/cde9b7f8-baf5-4bfa-b05f-882d7fce3da7
-- title:
--   Face boundary counts from a planar drawing
-- statement:
--   Extract the face boundary lengths of the connected drawing. Every length is at least three, their sum is twice the number of edges, and Euler's relation holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : Nat.le 3 (Fintype.card V)) : Exists (fun lengths : List Nat => And (forall l : Nat, List.Mem l lengths -> Nat.le 3 l) (And (lengths.sum = 2 * M.edgeFinset.card) (Fintype.card V + lengths.length = M.edgeFinset.card + 2))) := by sorry
