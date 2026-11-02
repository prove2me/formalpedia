-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:28.269705+00:00
-- url     : https://prove2.me/theorems/71dee139-0c7c-4650-9852-45d8d47fea47
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that is inclusion-maximal among drawable graphs on the same vertex type has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
