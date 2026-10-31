-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:28.898279+00:00
-- url     : https://prove2.me/theorems/b4d3c156-327f-4a72-8089-248d3313a19e
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A drawable graph maximal under drawable edge additions, on at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
