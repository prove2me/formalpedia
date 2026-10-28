-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_add_edge_across_components
-- name    : WilliamsonShmoys.planarDrawingOn_add_edge_across_components
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T16:33:32.26592+00:00
-- url     : https://prove2.me/theorems/e0795392-11c5-41d7-9e23-b888b43eab57
-- title:
--   A drawable disconnected graph admits a drawable edge extension
-- statement:
--   If a finite ordered vertex type carries a disconnected graph with a planar drawing, there are distinct nonadjacent vertices u and v and a drawable supergraph that adds the edge between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_add_edge_across_components
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hNotConnected : ¬ J.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧
      ∃ K : SimpleGraph V,
        J ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
