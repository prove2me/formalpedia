-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_face_degree_bound_b74a49f4
-- name    : WilliamsonShmoys.planar_connected_face_degree_bound_b74a49f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:19:44.982239+00:00
-- url     : https://prove2.me/theorems/8939dced-b9fa-47b4-99e3-2ca86836c1df
-- title:
--   Face boundary degree bound
-- statement:
--   For a connected simple graph with the specified planar drawing, any face count satisfying Euler's equation obeys the total face-boundary degree lower bound; summed face-boundary degrees are twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_face_degree_bound_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hConnected : K.Connected) (hCard : 3 ≤ Fintype.card V) (f : ℕ) (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2) : 3 * f ≤ 2 * K.edgeSet.ncard := by sorry
