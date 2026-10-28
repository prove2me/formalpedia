-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_edgeSet_subset
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:38:36.281608+00:00
-- url     : https://prove2.me/theorems/a99e83df-047e-45ba-9e13-053dfe5a21ab
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   A graph obtained by deleting edges from a graph with a planar drawing inherits a planar drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hGH : G.edgeSet ⊆ H.edgeSet) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
