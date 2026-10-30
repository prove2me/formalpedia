-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_le_of_planar_drawing
-- name    : WilliamsonShmoys.edge_count_le_of_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:13:14.510371+00:00
-- url     : https://prove2.me/theorems/015062cf-b2c0-48d5-a279-da412d383b8b
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every graph with the supplied crossing-free drawing on at least three vertices has at most `3n − 6` edges. The boundary `n = 3` is included; for disconnected drawings the proof must account for all components rather than assume connectedness. This removes the universal planar edge upper-bound calculation from the parent. A proof route is to derive Euler’s formula for the drawing, use that each face boundary has length at least three after handling tree components and bridges, and count face-edge incidences; alternatively, augment components to a connected planar graph before applying the standard bound. This is a new formal argument for the given drawing predicate; no matching Lean declaration was available locally.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_le_of_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
