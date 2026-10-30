-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_finite_edge_maximal_extension__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
-- name    : WilliamsonShmoys.planar_finite_edge_maximal_extension__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:43.900992+00:00
-- url     : https://prove2.me/theorems/67fa8ed9-e0b5-4d6e-a654-f64162c7a789
-- title:
--   Finite maximal planar extension
-- statement:
--   Every planar graph on a finite ordered vertex type has a planar supergraph on the same vertices whose edge count is at least the original’s and is maximum among all planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_finite_edge_maximal_extension__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ HasPlanarDrawingOn K /\
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       H.edgeFinset.card <= K.edgeFinset.card) /\
      (forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L ->
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
         letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         L.edgeFinset.card <= K.edgeFinset.card)) := by sorry
