-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarCompletionOn_card
-- name    : WilliamsonShmoys.planarCompletionOn_card
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:36:24.160132+00:00
-- url     : https://prove2.me/theorems/ccc1651f-d67f-4413-97b7-8b072e5530b3
-- title:
--   Planar graph completion to a triangulation
-- statement:
--   Every finite graph with at least three vertices and a planar drawing has a planar edge-supergraph on the same vertex set with exactly 3n−6 edges. This is a source-faithful completion-to-triangulation statement. Its concrete proof route is to extend the drawing to a maximal planar embedding, establish triangular face boundaries, and use Euler’s formula and face-edge double counting. The hypothesis n ≥ 3 is necessary for the formula; the result includes the n = 3 boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarCompletionOn_card
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V, G.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
