-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulation_289ce3bb
-- name    : WilliamsonShmoys.maximal_planar_edge_count_triangulation_289ce3bb
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:43:25.223131+00:00
-- url     : https://prove2.me/theorems/2b64a5f6-fa3e-480c-aaa9-a3e94662759c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges. A proof route derives connectedness and triangular faces from maximality, then combines Euler’s formula with face-edge incidence counting; the bridge and three-vertex cases must be handled in the formal argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_triangulation_289ce3bb
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
