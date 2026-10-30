-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_completion_lower_bound_repair_b095f50e
-- name    : WilliamsonShmoys.maximal_completion_lower_bound_repair_b095f50e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:25:52.502214+00:00
-- url     : https://prove2.me/theorems/04a22c47-b2c7-499e-b874-542ef0631830
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V| − 6 edges. Maximality forces connectedness and triangular faces; Euler's formula and face-edge incidence counting then give the bound, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_completion_lower_bound_repair_b095f50e
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V,
      W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by sorry
