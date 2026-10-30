-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_planar_edge_upper
-- name    : WilliamsonShmoys.maximal_planar_face_count_planar_edge_upper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:28:23.763309+00:00
-- url     : https://prove2.me/theorems/22808aa2-e7d7-4e69-ba56-f520b18487e9
-- title:
--   Planar edge upper bound for the face count theorem
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_planar_edge_upper
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
