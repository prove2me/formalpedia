-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:22.780205+00:00
-- url     : https://prove2.me/theorems/e972185b-4990-47b3-b33a-686d33f273ec
-- title:
--   An edge-maximal planar graph has the Euler bound with equality
-- statement:
--   A planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      ∀ u v, K.Adj u v → H.Adj u v) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
