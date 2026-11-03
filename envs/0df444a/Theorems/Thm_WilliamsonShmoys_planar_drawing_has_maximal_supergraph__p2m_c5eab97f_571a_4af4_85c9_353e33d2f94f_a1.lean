-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:04.943043+00:00
-- url     : https://prove2.me/theorems/926883cd-5ce8-410e-adef-3282b276c890
-- title:
--   Extend a drawn planar graph to a maximal planar supergraph
-- statement:
--   Any finite drawable planar simple graph on at least three vertices is contained in an inclusion-maximal drawable planar simple graph on the same vertex type. Finiteness gives a direct route by maximizing the number of edges among drawable supergraphs containing the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_c5eab97f_571a_4af4_85c9_353e33d2f94f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ K' : SimpleGraph V, K ≤ K' →
        WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K := by
  sorry
