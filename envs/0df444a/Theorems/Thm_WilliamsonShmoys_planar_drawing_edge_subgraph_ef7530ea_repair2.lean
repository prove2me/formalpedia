-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_subgraph_ef7530ea_repair2
-- name    : WilliamsonShmoys.planar_drawing_edge_subgraph_ef7530ea_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:05:53.892114+00:00
-- url     : https://prove2.me/theorems/747d7ae5-e571-4028-a1af-b9f97122885f
-- title:
--   Planar drawing restricts to an edge subgraph
-- statement:
--   Restricting the edge set of a graph with a planar drawing to an edge subgraph preserves the drawing. Keep the original points and arcs; the edge-inclusion hypothesis supplies each required edge condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_subgraph_ef7530ea_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : ∀ u v, G.Adj u v → H.Adj u v)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
