-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_mono__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
-- name    : WilliamsonShmoys.planar_drawing_mono__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:55.270783+00:00
-- url     : https://prove2.me/theorems/306c28be-81d6-44eb-ab29-deafc6389173
-- title:
--   Planar drawing is preserved under edge removal
-- statement:
--   If G is a subgraph of K and K has a planar drawing on the given ordered finite vertex type, then G has a planar drawing on the same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_mono__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
    {V : Type} [Fintype V] [LinearOrder V] {G K : SimpleGraph V}
    (hGK : G ≤ K) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
