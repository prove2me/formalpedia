-- Prove2me | Theorems.Thm_planar_drawing_edge_count_upper__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
-- name    : planar_drawing_edge_count_upper__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:28.715196+00:00
-- url     : https://prove2.me/theorems/45e747d5-3369-49e7-b0b7-b09895dc1bdd
-- title:
--   Planar drawing edge count upper bound
-- statement:
--   Any graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_drawing_edge_count_upper__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
