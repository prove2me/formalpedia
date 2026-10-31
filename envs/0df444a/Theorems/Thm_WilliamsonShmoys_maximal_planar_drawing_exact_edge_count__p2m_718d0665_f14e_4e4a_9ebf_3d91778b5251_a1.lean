-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:23:28.737986+00:00
-- url     : https://prove2.me/theorems/2881ff5d-60b0-4f02-aa50-a31ff757101b
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraph inclusion has exactly `3|V|−6` edges. The proof requires the planar-topology argument that a maximal planar drawing has triangular faces, followed by Euler's formula and face-edge counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
