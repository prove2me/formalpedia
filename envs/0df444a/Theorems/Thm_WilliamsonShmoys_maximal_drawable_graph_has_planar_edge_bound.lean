-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_planar_edge_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:12:43.095617+00:00
-- url     : https://prove2.me/theorems/71d18d81-b781-4d1d-8db7-e961ba28c810
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A maximal drawable simple graph with at least three vertices has at most three times its number of vertices minus six edges. The proof route is to derive connectedness and triangular faces from maximality, then apply Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hHmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → H.edgeSet ≠ K.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
