-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:27.814095+00:00
-- url     : https://prove2.me/theorems/ed45f97d-b8cc-4d3f-bccf-36b5559b7c87
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   This is the Euler-equation obligation for a finite connected graph with the stated crossing-free drawing. The vertex-size hypothesis is retained to align with the parent; it is not needed for Euler’s identity itself. The drawing definition supplies arcs whose interiors avoid vertices and whose pairwise intersections occur only at endpoints, which is the geometric input needed to extract a plane embedding. A proof route is to obtain the embedding’s rotation system and face walks, then apply Euler’s formula for connected plane maps. This removes the parent’s entire drawing-to-Euler step; that topological extraction and formula remain the core obligation for this child. The count includes the unbounded face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) : Exists fun f : Nat => Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
