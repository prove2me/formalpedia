-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:36:13.085298+00:00
-- url     : https://prove2.me/theorems/75470aa8-21fb-4723-a0a9-53d10a7cd9b1
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among planar supergraphs on its vertex type has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel _
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
