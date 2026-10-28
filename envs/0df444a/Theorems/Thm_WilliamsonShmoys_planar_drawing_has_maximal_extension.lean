-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:23:15.855067+00:00
-- url     : https://prove2.me/theorems/8cd24e3c-914c-42e7-a543-b7968ae48bf9
-- title:
--   Every finite drawable graph has a maximal drawable extension
-- statement:
--   Any finite drawable simple graph has a drawable extension on the same vertices that has no strictly larger drawable simple supergraph. The result also holds for vertex sets of size zero, one, or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ G : SimpleGraph V,
        H.edgeSet ⊆ G.edgeSet →
        HasPlanarDrawingOn G →
        G.edgeSet = H.edgeSet := by sorry
