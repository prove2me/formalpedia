-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_euler_face_count_b74a49f4
-- name    : WilliamsonShmoys.planar_connected_euler_face_count_b74a49f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:10:10.204245+00:00
-- url     : https://prove2.me/theorems/cf0c5020-99df-4018-b4de-698f5ab2e92d
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   Every connected graph with the specified planar drawing has a natural-number face count satisfying Euler's equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_euler_face_count_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hConnected : K.Connected) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
