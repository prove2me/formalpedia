-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:50:05.358131+00:00
-- url     : https://prove2.me/theorems/9a88f4ed-5392-4ef1-93d6-f90660b7c59e
-- title:
--   A maximal drawable graph has the exact planar edge count
-- statement:
--   If a drawable simple graph on at least three vertices has no proper drawable supergraph on the same vertex type, it has exactly \(3|V|-6\) edges. The proof formalizes the combinatorial embedding induced by the drawing, shows maximality forces a connected triangulation, and applies Euler’s formula and the two face incidences per edge. The lower bound on the number of vertices includes the boundary case of a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_exact_edge_count_dd73cac9_b90d_44a4_8977_1c0859414274
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
