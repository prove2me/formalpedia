-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeCount_le
-- name    : WilliamsonShmoys.planarDrawingOn_edgeCount_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:09:18.940401+00:00
-- url     : https://prove2.me/theorems/c0e03149-d8d6-4a8d-9c52-c2eeebb61f70
-- title:
--   Planar edge count upper bound
-- statement:
--   A drawable simple graph on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_edgeCount_le
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V) :
    S.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
