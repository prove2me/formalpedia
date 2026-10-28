-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:13:46.113165+00:00
-- url     : https://prove2.me/theorems/93f8fc7f-61d6-4435-b211-2fb21e6a8bea
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs. Choose a drawable supergraph with the largest edge-set cardinality; the original graph makes the candidate class nonempty, and strict inclusion increases edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      LE.le Z W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V,
        LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W := by sorry
