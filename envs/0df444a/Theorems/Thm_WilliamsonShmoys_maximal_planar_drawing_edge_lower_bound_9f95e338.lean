-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_9f95e338
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_9f95e338
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:59:23.16929+00:00
-- url     : https://prove2.me/theorems/43a76282-a988-413a-89ad-635427becaba
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A graph with a drawing satisfying HasPlanarDrawingOn that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges when |V|≥3. The proof route is to formalize the embedding's faces, use maximality to rule out any face that can be enlarged by adding an edge, establish the required connectivity and triangular-face properties, and apply Euler's formula. The case |V|=3 remains within the hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_9f95e338
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  sorry
