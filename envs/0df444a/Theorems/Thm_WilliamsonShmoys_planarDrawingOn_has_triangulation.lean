-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_triangulation
-- name    : WilliamsonShmoys.planarDrawingOn_has_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:27:45.320605+00:00
-- url     : https://prove2.me/theorems/a27d7dd0-24ea-47a8-bd63-fd7c1b6c5759
-- title:
--   Planar drawing admits a triangulation completion
-- statement:
--   Every connected graph with a crossing-free drawing on a finite ordered vertex type of size at least three is contained in a planar graph on the same vertices with exactly 3n−6 edges. The child packages the planar completion and Euler-counting argument, leaving the parent to apply maximality and transfer the edge count. Its hypotheses cover the standard connected triangulation boundary cases; a proof route is to take an edge-maximal planar supergraph, rule out nontriangular faces by adding an edge, then count face-edge incidences with Euler’s formula. Formalizing this route for the supplied continuous-arc drawing predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawingOn_has_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by sorry
