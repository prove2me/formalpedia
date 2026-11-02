-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:03.948002+00:00
-- url     : https://prove2.me/theorems/8ea6d6e0-f206-47b7-9e0b-83b7a69a6862
-- title:
--   Edge-maximal planar graphs meet the Euler edge lower bound
-- statement:
--   A planar graph on at least three vertices that admits no proper planar supergraph on the same vertex type has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      ∀ u v, K.Adj u v → H.Adj u v) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      3 * Fintype.card V ≤ H.edgeFinset.card + 6) := by sorry
