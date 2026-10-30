-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:25:38.756156+00:00
-- url     : https://prove2.me/theorems/a41ba058-0926-4932-8131-302826679a62
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K := by sorry
