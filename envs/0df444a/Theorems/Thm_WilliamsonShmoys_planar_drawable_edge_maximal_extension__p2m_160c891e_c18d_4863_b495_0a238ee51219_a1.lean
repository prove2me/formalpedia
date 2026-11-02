-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_maximal_extension__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
-- name    : WilliamsonShmoys.planar_drawable_edge_maximal_extension__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:33.838081+00:00
-- url     : https://prove2.me/theorems/dc4c57d6-8c7b-40a5-8d0c-5d35fb58c653
-- title:
--   Finite maximal drawable extension
-- statement:
--   Among drawable supergraphs of M on the same finite vertex type, there is one with maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_edge_maximal_extension__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K →
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj
         letI : Fintype ↑K.edgeSet := Fintype.ofFinite _
         letI : DecidableRel N.Adj := Classical.decRel N.Adj
         letI : Fintype ↑N.edgeSet := Fintype.ofFinite _
         K.edgeFinset.card ≤ N.edgeFinset.card)) := by
  sorry
