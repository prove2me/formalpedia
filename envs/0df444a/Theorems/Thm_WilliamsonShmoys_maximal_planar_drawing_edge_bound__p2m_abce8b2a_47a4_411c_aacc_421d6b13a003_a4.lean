-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:14.8085+00:00
-- url     : https://prove2.me/theorems/2fdbe618-fdb5-40d5-afa9-43a53e53fa32
-- title:
--   Edge lower bound for maximal planar drawings
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph has at least 3|V|−6 edges. The proof route is to use Jordan separation to show a maximal drawing is connected and every face is triangular, then apply Euler’s formula and count face-edge incidences. The strict vertex lower bound is retained for the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
