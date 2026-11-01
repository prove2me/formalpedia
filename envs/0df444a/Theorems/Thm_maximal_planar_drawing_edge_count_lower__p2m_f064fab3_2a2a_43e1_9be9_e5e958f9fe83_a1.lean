-- Prove2me | Theorems.Thm_maximal_planar_drawing_edge_count_lower__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
-- name    : maximal_planar_drawing_edge_count_lower__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:16:35.214981+00:00
-- url     : https://prove2.me/theorems/b3e85d1d-c054-4e02-815f-118f1fda4ccd
-- title:
--   Maximal planar drawing edge count lower bound
-- statement:
--   A graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem maximal_planar_drawing_edge_count_lower__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeFinset.card + 6 := by sorry
