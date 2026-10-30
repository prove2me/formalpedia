-- Prove2me | Theorems.Thm_planar_drawingOn_has_supergraph_edge_bound
-- name    : planar_drawingOn_has_supergraph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:06:16.252127+00:00
-- url     : https://prove2.me/theorems/e691469b-b4f6-4886-a149-aa66a91db182
-- title:
--   Planar drawing extends to a supergraph meeting the planar edge bound
-- statement:
--   For a finite ordered vertex type with at least three vertices, every graph with a crossing-free drawing has a planar supergraph on the same vertices with at least 3|V|−6 edges. The bound is consistent at |V| = 3, where a maximal extension is a triangle. A concrete proof route is to add edges while preserving the drawing until the extension is maximal, prove its faces are triangular, then use Euler’s formula and the face-degree count. This is the main remaining obligation; the supplied local definition source does not contain that proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planar_drawingOn_has_supergraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V, G <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
