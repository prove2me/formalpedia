-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261027_job59ad8832
-- name    : WilliamsonShmoys.maximal_planar_edge_count_20261027_job59ad8832
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:44:43.423503+00:00
-- url     : https://prove2.me/theorems/9e56ac28-c599-4e0f-acc6-2359074c43f9
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   For at least three vertices, an inclusion-maximal graph admitting the supplied crossing-free drawing predicate has exactly 3n−6 edges. The lower bound on the vertex count is retained because the triangulation edge formula does not hold for all smaller cases. A proof route is to show maximality forces connectedness and triangular faces, establish Euler’s formula for the resulting plane embedding, and count each edge twice in the face boundaries. This is the remaining topological and counting core.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_20261027_job59ad8832
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
