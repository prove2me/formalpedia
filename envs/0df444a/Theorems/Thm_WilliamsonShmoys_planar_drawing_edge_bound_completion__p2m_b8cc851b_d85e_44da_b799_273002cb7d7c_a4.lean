-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:22:08.030994+00:00
-- url     : https://prove2.me/theorems/f34871aa-4b26-4166-99f3-d88e1cde8300
-- title:
--   Drawable completion attaining the planar edge bound
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      N <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
