-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
-- name    : WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:26:26.611383+00:00
-- url     : https://prove2.me/theorems/6afa16d8-44ba-4055-8683-f29063f5c38c
-- title:
--   A disconnected planar drawing admits a strict drawable supergraph
-- statement:
--   Any disconnected graph on at least three vertices with a crossing-free drawing has a strict supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ J : SimpleGraph V, H ≤ J ∧ J ≠ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn J := by sorry
