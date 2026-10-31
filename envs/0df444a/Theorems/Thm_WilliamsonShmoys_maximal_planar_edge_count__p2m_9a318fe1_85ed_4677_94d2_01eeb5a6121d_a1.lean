-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:28.032462+00:00
-- url     : https://prove2.me/theorems/5c7e3e9c-a96f-48f5-9248-611aedcd18a3
-- title:
--   Euler edge count for an edge-maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that has a crossing-free drawing and is maximal under planar edge addition has exactly 3|V|−6 edges. The proof route is to show maximality makes the drawing a connected triangulation, then combine Euler’s formula with the count of edge incidences around triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ M.edgeSet) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
