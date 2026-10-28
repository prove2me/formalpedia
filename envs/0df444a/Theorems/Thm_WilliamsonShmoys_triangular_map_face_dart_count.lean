-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_face_dart_count
-- name    : WilliamsonShmoys.triangular_map_face_dart_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:00:37.70208+00:00
-- url     : https://prove2.me/theorems/665cf6ae-b005-45ca-be40-905fc7888941
-- title:
--   Face count from triangular map darts
-- statement:
--   The triangular map’s m faces contribute 3m face corners, while each undirected edge contributes two oriented darts, so 3m equals twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap

set_option autoImplicit false

theorem WilliamsonShmoys.triangular_map_face_dart_count
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    {m : Nat}
    (M : WilliamsonShmoys.TriangularMap H (Fin m)) :
    3 * m = 2 * H.edgeSet.ncard := by sorry
