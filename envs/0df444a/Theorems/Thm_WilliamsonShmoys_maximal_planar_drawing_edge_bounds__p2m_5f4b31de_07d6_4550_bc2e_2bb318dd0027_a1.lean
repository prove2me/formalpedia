-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bounds__p2m_5f4b31de_07d6_4550_bc2e_2bb318dd0027_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bounds__p2m_5f4b31de_07d6_4550_bc2e_2bb318dd0027_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:19.529144+00:00
-- url     : https://prove2.me/theorems/6524a699-0954-4f2d-8bab-0691ea13c3c9
-- title:
--   Edge bounds for a maximal planar drawing
-- statement:
--   A maximal simple graph with a crossing-free drawing and at least three vertices has enough edges for |V| ≤ |E| + 2 and no more than the planar bound |E| + 6 ≤ 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bounds__p2m_5f4b31de_07d6_4550_bc2e_2bb318dd0027_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    Fintype.card V ≤ H.edgeSet.ncard + 2 ∧
      H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
