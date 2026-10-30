-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
-- name    : WilliamsonShmoys.maximal_drawable_graph_connected__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:52:38.731057+00:00
-- url     : https://prove2.me/theorems/af2f55a3-cc79-4d62-b424-a014133823d3
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   Maximality among graphs admitting the specified crossing-free drawing forces connectedness. This removes the topological part of the parent argument. A proof can join vertices from different components by a new arc avoiding the finite existing drawing, then contradict maximality. The hypothesis of at least three vertices is retained exactly; the claim makes no assertion in smaller boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_connected__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.Connected := by sorry
