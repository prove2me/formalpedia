-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_edgeCount__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
-- name    : WilliamsonShmoys.maximalPlanar_edgeCount__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:24:52.774233+00:00
-- url     : https://prove2.me/theorems/21a5024a-68c6-4092-ae33-cef64e9ed718
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3 * |V| - 6` edges. This removes the counting step from the parent. An independent proof route is to establish from maximality that the drawing is connected and every face is triangular, then combine Euler’s formula with the fact that each edge borders two face sides. The lower bound of three vertices is essential to this triangulation conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanar_edgeCount__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      HasPlanarDrawingOn M →
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset ⊆ M.edgeFinset) →
      (letI : DecidableRel L.Adj := dL
       letI : DecidableRel M.Adj := dM
       L.edgeFinset = M.edgeFinset))
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
