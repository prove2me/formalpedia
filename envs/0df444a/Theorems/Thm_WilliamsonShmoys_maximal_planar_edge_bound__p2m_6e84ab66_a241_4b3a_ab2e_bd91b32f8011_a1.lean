-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:31.398662+00:00
-- url     : https://prove2.me/theorems/d5765fc6-2061-49c6-883d-a2bbbc9ebfd2
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A connected simple graph on at least three vertices that has a crossing-free drawing and is maximal among planar supergraphs on its vertex set has at most 3|V| − 6 edges. The proof route is to show maximality forces triangular faces and then count with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1 {V : Type} [Fintype V] [LinearOrder V] {H : SimpleGraph V} [DecidableRel H.Adj] (hplanar : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hconn : H.Connected) (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K ≤ H) : H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
