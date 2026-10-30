-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:04:18.109658+00:00
-- url     : https://prove2.me/theorems/e2b131f7-3fa6-4028-b77b-f247189916b8
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices. The proof route is finite maximization of edge count among drawable supergraphs; the family is nonempty because it contains G. This isolates the completion step without assuming connectedness or changing the vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
