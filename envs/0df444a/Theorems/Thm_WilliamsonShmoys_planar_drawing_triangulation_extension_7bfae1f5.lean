-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_7bfae1f5
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_7bfae1f5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:45:45.573265+00:00
-- url     : https://prove2.me/theorems/ca2fe8f1-c3cb-4014-879e-982f2e091a93
-- title:
--   Extend a drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly `3|V|−6` edges. The vertex-count lower bound is required for a triangulation on the given vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_7bfae1f5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, HasPlanarDrawingOn W ∧
      (∀ u v, G.Adj u v → W.Adj u v) ∧
      W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
