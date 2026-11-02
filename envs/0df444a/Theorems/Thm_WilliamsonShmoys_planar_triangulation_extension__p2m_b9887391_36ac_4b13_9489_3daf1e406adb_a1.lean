-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b9887391_36ac_4b13_9489_3daf1e406adb_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_b9887391_36ac_4b13_9489_3daf1e406adb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:34:27.238284+00:00
-- url     : https://prove2.me/theorems/6d98c2a3-7d62-42a8-a794-93d41b1b40ef
-- title:
--   Planar triangulation extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_b9887391_36ac_4b13_9489_3daf1e406adb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : Fintype ↥K.edgeSet := Fintype.ofFinite _
       K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  sorry
