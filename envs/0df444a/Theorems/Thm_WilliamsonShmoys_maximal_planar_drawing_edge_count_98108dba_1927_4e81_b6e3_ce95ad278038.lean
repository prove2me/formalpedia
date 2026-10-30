-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:16:45.134712+00:00
-- url     : https://prove2.me/theorems/5284bedf-03a3-4982-aff7-5ebd00e5e8a0
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices with no drawable strict supergraph on the same vertex type has exactly `3|V|−6` edges. Prove this by deriving the maximal-planar structure from the given drawing predicate and applying Euler’s formula; at three vertices maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
