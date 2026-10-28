-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_of_le
-- name    : WilliamsonShmoys.planarDrawingOn_of_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:21:13.181918+00:00
-- url     : https://prove2.me/theorems/5e73815d-776a-48c5-92bf-87f50afcb9ef
-- title:
--   Planar drawing inherited by subgraphs
-- statement:
--   A graph on the same ordered finite vertex type inherits a crossing-free drawing from any graph containing all its edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_of_le
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
