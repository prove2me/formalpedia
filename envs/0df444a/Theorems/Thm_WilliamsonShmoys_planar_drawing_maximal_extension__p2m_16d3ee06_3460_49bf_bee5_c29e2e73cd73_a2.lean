-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:40:20.900806+00:00
-- url     : https://prove2.me/theorems/0d55c294-ea6d-4f9f-a448-4b66814798e5
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every graph with the specified drawing on a finite ordered vertex type is contained in a drawable supergraph that is maximal among planar supergraphs on that same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, HasPlanarDrawingOn J → H ≤ J → J = H) ∧
      G.edgeFinset.card ≤ H.edgeFinset.card := by sorry
