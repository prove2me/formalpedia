-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:14:53.793966+00:00
-- url     : https://prove2.me/theorems/b07b2cea-077c-4214-a610-9ab8bd281015
-- title:
--   Planar triangulation extension on a fixed vertex set
-- statement:
--   Any planar simple graph on at least three vertices is a subgraph of a planar triangulation on the same vertex set, whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ HasPlanarDrawingOn L /\
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
         L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
