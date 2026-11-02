-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_53978d9a_ff21_4c38_b5ef_6e6d6a6a4bf9_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_53978d9a_ff21_4c38_b5ef_6e6d6a6a4bf9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:53.548276+00:00
-- url     : https://prove2.me/theorems/aeb54813-f1d1-4dac-8fed-a439903a5d98
-- title:
--   Planar edge upper bound from a drawing
-- statement:
--   A graph on at least three vertices with the supplied crossing-free drawing has at most `3 * |V| - 6` edges, written as `edgeFinset.card + 6 ≤ 3 * |V|`. The statement retains the target's exact drawing predicate and includes the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_53978d9a_ff21_4c38_b5ef_6e6d6a6a4bf9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hKdraw : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
