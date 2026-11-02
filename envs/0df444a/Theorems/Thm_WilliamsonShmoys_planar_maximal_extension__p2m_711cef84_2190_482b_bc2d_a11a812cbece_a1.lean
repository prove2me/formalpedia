-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:27.762194+00:00
-- url     : https://prove2.me/theorems/bf88fb9b-d414-423e-a554-a94a80021b01
-- title:
--   Every planar drawing extends to an edge-maximal planar graph
-- statement:
--   On a fixed finite vertex type, any graph with a planar drawing has a planar supergraph that is maximal under edge inclusion, and the supergraph has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       L.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ u v, H.Adj u v → K.Adj u v) →
        ∀ u v, K.Adj u v → H.Adj u v) := by sorry
