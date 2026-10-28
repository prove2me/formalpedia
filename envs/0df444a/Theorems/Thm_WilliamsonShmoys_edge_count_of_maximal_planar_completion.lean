-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_completion
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:08:17.102949+00:00
-- url     : https://prove2.me/theorems/b4169ffc-b14b-4a6e-af8f-153d5f82e0d4
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly `3|V|−6` edges. This removes the planar topology and counting from the target. A proof route is to establish that a maximal planar embedding is connected and every face is triangular, apply Euler’s formula, and count edge-face incidences. The drawing hypotheses and the lower bound on the vertex count must be retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
