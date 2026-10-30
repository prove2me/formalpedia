-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- name    : WilliamsonShmoys.planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:43.79127+00:00
-- url     : https://prove2.me/theorems/f85cf95c-259e-403f-a3bb-5b4078926a26
-- title:
--   Planar graph edge upper bound
-- statement:
--   Every finite drawable simple graph on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
