-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:59:41.747988+00:00
-- url     : https://prove2.me/theorems/70223eb0-37a5-453d-b117-2e1715a81eea
-- title:
--   A maximal planar drawing has the sharp edge count
-- statement:
--   A finite simple graph with at least three vertices that is maximal among planar supergraphs has exactly `3 * card V - 6` edges. The bound is necessary for the three-vertex case: maximality yields the triangle. For larger cases, the proof route is to establish connectedness and triangular faces from edge-maximality, count face-edge incidences, and combine that count with Euler’s formula. This child removes the topological augmentation and Euler argument from the parent; that remains the core unproved obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
