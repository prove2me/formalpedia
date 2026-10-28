-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_maximal_6357fee1_f927_4c5b_a160_dca513168a22
-- name    : WilliamsonShmoys.planar_drawing_extension_to_maximal_6357fee1_f927_4c5b_a160_dca513168a22
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:12:02.737626+00:00
-- url     : https://prove2.me/theorems/c9a0435e-7fe7-433f-bfc0-746c7bd7e697
-- title:
--   Finite maximal planar extension
-- statement:
--   Extend any finite graph with a crossing-free drawing to a planar supergraph on the same vertex type that is maximal among planar supergraphs and has at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extension_to_maximal_6357fee1_f927_4c5b_a160_dca513168a22
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (H <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (H.edgeSet.ncard <= K.edgeSet.ncard)
          (forall L : SimpleGraph V, K <= L ->
            WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K))) := by sorry
