-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_maximizer
-- name    : WilliamsonShmoys.exists_planar_edge_maximizer
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:59:53.534104+00:00
-- url     : https://prove2.me/theorems/c5621e40-5a5e-4f4e-99f4-ecb1743bdbdf
-- title:
--   Drawable maximal planar augmentation has the maximal edge count
-- statement:
--   Every connected drawable simple graph on at least three vertices is contained in a drawable graph on the same vertex type with the maximal planar edge count. The edge-count comparison is included so the parent can derive its bound directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_edge_maximizer
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
