-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_planar_triangulation_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:46:35.304894+00:00
-- url     : https://prove2.me/theorems/4b48afbc-2cb8-4c5a-815f-5c1a79606e63
-- title:
--   A maximal planar graph has the triangulation edge count
-- statement:
--   Every edge-maximal simple graph admitting the specified crossing-free drawing has exactly 3|V|−6 edges when |V| ≥ 3. This contains the remaining planar-topology and counting work. A proof route is to establish that maximality forces a connected triangulation, then apply Euler’s formula and the face-edge incidence count. The condition |V| ≥ 3 covers K₃, whose count is 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
