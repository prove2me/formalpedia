-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_maximal_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:41:58.00839+00:00
-- url     : https://prove2.me/theorems/ccfac8a1-8bd1-4174-903b-419cc64e61a7
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable proper supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
