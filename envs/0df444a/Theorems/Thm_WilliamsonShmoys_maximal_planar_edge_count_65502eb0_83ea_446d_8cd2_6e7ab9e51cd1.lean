-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:04:10.463995+00:00
-- url     : https://prove2.me/theorems/e8f101b4-17d7-4d2f-a33b-12f5af59688a
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   If a graph with the supplied planar drawing is edge-maximal among planar graphs on the same vertices and |V| ≥ 3, then it has exactly 3|V|−6 edges. The proof route is to use maximality to establish connectedness and triangular faces, apply Euler’s formula, and count each edge twice in the face boundaries. At |V| = 3, this gives the triangle case with three edges. This is the remaining topological core of the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J →
      H.edgeSet ⊆ J.edgeSet → J.edgeSet ⊆ H.edgeSet)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
