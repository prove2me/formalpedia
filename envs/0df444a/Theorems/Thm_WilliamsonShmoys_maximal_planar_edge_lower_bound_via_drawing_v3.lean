-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_via_drawing_v3
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_via_drawing_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:09:37.216197+00:00
-- url     : https://prove2.me/theorems/a1ee501e-8bac-4bc3-ae68-41fa4f076db4
-- title:
--   Edge lower bound for a maximal graph with a planar drawing
-- statement:
--   A graph on at least three vertices with the stated drawing and no strictly larger planar supergraph on the same vertex type has at least \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_via_drawing_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
