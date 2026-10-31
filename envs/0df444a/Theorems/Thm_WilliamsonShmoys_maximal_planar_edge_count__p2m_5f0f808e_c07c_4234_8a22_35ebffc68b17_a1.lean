-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:43:26.500118+00:00
-- url     : https://prove2.me/theorems/c356afa4-3905-47c7-8a37-a6d010ebe354
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph on the same vertex set has exactly 3|V|−6 edges. This removes the face-counting and Euler-characteristic work from the parent. A proof route is to take a planar embedding, show maximality rules out every face of length greater than three because a diagonal could be added inside it, then combine Euler’s formula with the fact that each edge is incident to two face sides. The remaining core obligation is to formalize those topological facts for the continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V, H ≤ L → L ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
