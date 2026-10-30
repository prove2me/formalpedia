-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_maximality
-- name    : WilliamsonShmoys.maximal_planar_edge_count_from_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:39:46.812505+00:00
-- url     : https://prove2.me/theorems/fa44c7bf-cefe-4665-a89c-a65f46677ffc
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The three-vertex boundary case is the triangle. The proof uses maximality to obtain triangular faces, then Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_from_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
