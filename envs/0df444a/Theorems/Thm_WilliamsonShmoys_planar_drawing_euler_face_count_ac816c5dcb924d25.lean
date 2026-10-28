-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_ac816c5dcb924d25
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_ac816c5dcb924d25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:03:44.210721+00:00
-- url     : https://prove2.me/theorems/68800381-c65d-41d5-99e5-3dbc09c248bd
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   The supplied crossing-free drawing of a finite connected graph determines a face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count_ac816c5dcb924d25
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
