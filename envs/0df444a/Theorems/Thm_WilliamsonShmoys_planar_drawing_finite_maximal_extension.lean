-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:10:55.798519+00:00
-- url     : https://prove2.me/theorems/08f590bd-49b8-41b4-8198-808310a9788b
-- title:
--   Planar drawing extends to a finite maximal supergraph
-- statement:
--   A finite simply drawn planar simple graph on at least three vertices has a simply drawn planar supergraph on the same vertex set that is maximal among such supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_finite_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
