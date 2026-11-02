-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:20.378581+00:00
-- url     : https://prove2.me/theorems/5d6e3508-c11e-4337-a63b-6a8f12f05f58
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type. Finiteness permits choosing a drawable supergraph with the greatest number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  sorry
