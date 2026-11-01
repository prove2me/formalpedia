-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_subgraph__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_subgraph__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:41.739202+00:00
-- url     : https://prove2.me/theorems/cb49cc41-2ac0-46b1-906d-05eb5912d9db
-- title:
--   Planar drawing restricts to subgraphs
-- statement:
--   If G is a subgraph of G' on the same ordered vertex type and G' has a crossing-free drawing, then G has one too.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_subgraph__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G G' : SimpleGraph V} (h : G ≤ G')
    (hG' : WilliamsonShmoys.HasPlanarDrawingOn G') :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
