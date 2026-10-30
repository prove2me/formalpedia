-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_extension_below_bound
-- name    : WilliamsonShmoys.planar_edge_extension_below_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:15:52.708851+00:00
-- url     : https://prove2.me/theorems/42920628-295c-4315-9cee-c009d6b05e33
-- title:
--   A planar graph below the triangulation bound admits an edge extension
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every graph with a crossing-free drawing and fewer than $3|V|-6$ edges has a crossing-free strict supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_extension_below_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcount : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      Set.Subset G.edgeSet S.edgeSet ∧
      S.edgeSet ≠ G.edgeSet := by sorry
