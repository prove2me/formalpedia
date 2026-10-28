-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_of_disconnected
-- name    : WilliamsonShmoys.planar_supergraph_of_disconnected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:22:42.222661+00:00
-- url     : https://prove2.me/theorems/e285668e-edc8-44a9-b3e1-579f75c4524d
-- title:
--   A disconnected drawable graph has a strict drawable supergraph
-- statement:
--   For a finite linearly ordered vertex type with at least three elements, every disconnected graph with a crossing-free drawing has a strictly larger supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_of_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hDisconnected : ¬ L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
