-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_supergraph_exists_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_supergraph_exists_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:28:56.38934+00:00
-- url     : https://prove2.me/theorems/ff36fd69-c911-46c4-83c8-2a8607afea89
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_supergraph_exists_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V =>
      G <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      forall N : SimpleGraph V,
        M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N ->
        N <= M := by sorry
