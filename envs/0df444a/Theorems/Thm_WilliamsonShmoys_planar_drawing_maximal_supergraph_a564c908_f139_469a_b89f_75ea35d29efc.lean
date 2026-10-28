-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_a564c908_f139_469a_b89f_75ea35d29efc
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_a564c908_f139_469a_b89f_75ea35d29efc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:14:56.33188+00:00
-- url     : https://prove2.me/theorems/5821f0dd-d3fc-4f24-89f5-23b7e47788d4
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_a564c908_f139_469a_b89f_75ea35d29efc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph V,
      G <= N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph V, N <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M <= N := by sorry
