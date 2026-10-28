-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_71ca74e3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_71ca74e3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:14:25.285838+00:00
-- url     : https://prove2.me/theorems/9525bc2d-6e0d-4029-99f4-e9901dcdc86f
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof route is to show maximality forces connectedness and triangular faces, then count face-edge incidences and apply Euler’s formula, handling the three-vertex case directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_71ca74e3
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V,
      LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = W.edgeSet.ncard := by sorry
