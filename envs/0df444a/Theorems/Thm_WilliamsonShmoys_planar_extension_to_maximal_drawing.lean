-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_maximal_drawing
-- name    : WilliamsonShmoys.planar_extension_to_maximal_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:18:58.657228+00:00
-- url     : https://prove2.me/theorems/b85d5091-f0b7-455f-b589-2e97a94facae
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Every graph with a drawing on a finite vertex type has a planar supergraph maximal under edge inclusion. Choose a maximum edge set among the finitely many planar supergraphs containing the input; any strictly larger planar extension would contradict maximality of its cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_maximal_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by sorry
