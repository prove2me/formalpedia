-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:24:22.140818+00:00
-- url     : https://prove2.me/theorems/abda2b28-0ec6-4f5c-9d0b-7e00290f44a0
-- title:
--   Edge count of maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly `3n - 6` edges. The proof can pass from maximality to a connected plane embedding with triangular faces, then count edges using Euler’s formula and face-edge incidence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q)
    (hCard : 3 ≤ Fintype.card V) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
