-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edgeSet_ncard_le_of_connected
-- name    : WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le_of_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:29:52.91323+00:00
-- url     : https://prove2.me/theorems/d4a780a1-0e30-41cf-aea2-2a8b33d329cd
-- title:
--   Planar edge bound for connected graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le_of_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V)
    (hConnected : J.Connected) :
    J.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
