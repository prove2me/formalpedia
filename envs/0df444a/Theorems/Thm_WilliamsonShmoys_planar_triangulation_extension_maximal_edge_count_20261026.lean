-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_edge_count_20261026
-- name    : WilliamsonShmoys.planar_triangulation_extension_maximal_edge_count_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:05:15.696618+00:00
-- url     : https://prove2.me/theorems/4dbe730e-6943-45f1-848c-d4d45684fcdf
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. Its independent proof route is to pass from a drawing to a plane embedding, establish that maximality forces every face to be triangular, and derive the edge count from Euler’s formula. The lower bound on the number of vertices is retained for the planar edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_maximal_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  sorry
