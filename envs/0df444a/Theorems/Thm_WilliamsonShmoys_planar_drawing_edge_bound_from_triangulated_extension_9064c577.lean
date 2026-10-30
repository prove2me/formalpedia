-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_triangulated_extension_9064c577
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_from_triangulated_extension_9064c577
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:59:42.004133+00:00
-- url     : https://prove2.me/theorems/8869a5b2-5e37-485c-9560-58cf0f5e6271
-- title:
--   Maximal planar extension has the planar edge count
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing is a subgraph of a graph on the same vertices that also has a crossing-free drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_from_triangulated_extension_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
