-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
-- name    : WilliamsonShmoys.planar_maximal_edge_count__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:44.423348+00:00
-- url     : https://prove2.me/theorems/fc022252-a12f-4a07-aef3-b2bbba00d482
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices whose planar supergraphs on the same vertices never have more edges has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L ->
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       L.edgeFinset.card <= K.edgeFinset.card)) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
