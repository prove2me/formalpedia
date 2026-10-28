-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_maximal_graph_bound
-- name    : WilliamsonShmoys.planar_simple_edge_bound_maximal_graph_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:57:44.626251+00:00
-- url     : https://prove2.me/theorems/dd15e4ab-0697-4b8a-a7a1-b89e7c297b2d
-- title:
--   Edge bound for a maximal drawn graph
-- statement:
--   A maximal graph admitting the specified drawing has at most 3|V|−6 edges when |V|≥3. The proof route is to show maximality forces a connected triangulated embedding, then use Euler’s formula and count the three edge-sides per face. The boundary case |V|=3 is included; the Euler/triangulation argument must preserve the simple-graph and drawing hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_bound_maximal_graph_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
