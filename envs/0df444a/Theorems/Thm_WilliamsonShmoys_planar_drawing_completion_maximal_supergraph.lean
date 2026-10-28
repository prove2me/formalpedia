-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_completion_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:28:37.110981+00:00
-- url     : https://prove2.me/theorems/d4f94ae8-c6cd-4835-b2ca-8552ff4d28ea
-- title:
--   Maximal planar supergraph completion
-- statement:
--   Every finite graph with a crossing-free drawing has a planar supergraph on the same vertex type that is maximal under edge inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      LE.le U W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        (∀ X : SimpleGraph V, LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W) := by sorry
