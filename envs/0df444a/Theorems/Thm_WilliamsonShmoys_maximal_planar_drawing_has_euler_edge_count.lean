-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:23:25.100188+00:00
-- url     : https://prove2.me/theorems/0e574c9e-7a53-442a-9023-2328237592d2
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that is maximal among drawable edge supergraphs has exactly 3|V| − 6 edges. The proof must formalize the maximal planar graph edge-count argument for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      L.edgeSet ⊆ K.edgeSet → K.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
