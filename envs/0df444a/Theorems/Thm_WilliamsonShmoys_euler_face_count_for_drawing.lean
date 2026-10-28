-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_for_drawing
-- name    : WilliamsonShmoys.euler_face_count_for_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:34:40.045989+00:00
-- url     : https://prove2.me/theorems/0de2ca16-7239-470f-846d-66f5c5bd9286
-- title:
--   Euler face count for a connected drawing
-- statement:
--   A finite connected graph with a drawing satisfying HasPlanarDrawingOn has a natural-number face count f satisfying Euler’s formula |V| + f = |E| + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_face_count_for_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
