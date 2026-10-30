-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:07:33.093371+00:00
-- url     : https://prove2.me/theorems/e8725f7b-8abc-42b9-8220-9bc2308952b7
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable edge supergraph on the same vertices has exactly 3|V|−6 edges. The lower bound of three vertices is essential for this count: maximal drawable graphs on fewer vertices do not satisfy the formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      M.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
