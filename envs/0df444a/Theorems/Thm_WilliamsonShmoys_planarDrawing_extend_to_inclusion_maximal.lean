-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_extend_to_inclusion_maximal
-- name    : WilliamsonShmoys.planarDrawing_extend_to_inclusion_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:39:04.250198+00:00
-- url     : https://prove2.me/theorems/cf3cd5bb-0abe-4e1d-b3a0-206427d7fa97
-- title:
--   Extend a planar drawing to an inclusion-maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion among planar supergraphs. This follows by maximizing the edge set over the finite collection of eligible simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_extend_to_inclusion_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        Set.Subset H.edgeSet K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        Set.Subset K.edgeSet H.edgeSet := by sorry
