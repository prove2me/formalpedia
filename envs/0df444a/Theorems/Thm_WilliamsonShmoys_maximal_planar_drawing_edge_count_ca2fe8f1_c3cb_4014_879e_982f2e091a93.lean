-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_ca2fe8f1_c3cb_4014_879e_982f2e091a93
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_ca2fe8f1_c3cb_4014_879e_982f2e091a93
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:07:03.271117+00:00
-- url     : https://prove2.me/theorems/daaeac1d-1a5f-4c20-8883-0d30cbc755f4
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly `3|V|−6` edges. This is the remaining core obligation; it removes the edge-count argument from the parent. A concrete proof route is to use maximality to rule out non-triangular faces, establish connectedness and the face-incidence count for the given drawing, and combine these with Euler’s formula. The vertex lower bound is necessary to obtain a triangulation on the fixed vertex set; it is preserved explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_ca2fe8f1_c3cb_4014_879e_982f2e091a93
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) →
      ∀ u v, X.Adj u v → W.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
