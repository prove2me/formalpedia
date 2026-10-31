-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:55.349388+00:00
-- url     : https://prove2.me/theorems/700821ca-25b4-460b-96d1-6f5eea16c5cc
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Any connected drawn graph on a finite vertex type has a connected drawn supergraph on the same vertices that is maximal in edge count among drawn supergraphs and has at least as many edges as the original graph. Finiteness of the set of possible graphs gives the maximizing extension; connectedness follows because it contains the connected graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  sorry
