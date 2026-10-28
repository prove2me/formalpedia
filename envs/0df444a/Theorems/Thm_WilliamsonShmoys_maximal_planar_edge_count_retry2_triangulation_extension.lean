-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_retry2_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_edge_count_retry2_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:15:36.668481+00:00
-- url     : https://prove2.me/theorems/9e9bab3a-ed2f-44d4-8020-d51853fbec93
-- title:
--   Edge count of a maximal planar supergraph
-- statement:
--   A connected, edge-maximal simple planar graph on at least three vertices has exactly 3|V|−6 edges. The proof uses maximality to force triangular faces, followed by Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_retry2_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
