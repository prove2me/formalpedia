-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:12:48.772755+00:00
-- url     : https://prove2.me/theorems/33f2abb6-4890-4032-9845-f9099e3af4d0
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges. The proof route is maximal planar extension followed by connectedness, triangular faces, and Euler counting; the extension and face argument are the main remaining mathematical obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
