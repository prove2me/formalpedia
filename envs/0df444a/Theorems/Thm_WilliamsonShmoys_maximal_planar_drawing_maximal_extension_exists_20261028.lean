-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_maximal_extension_exists_20261028
-- name    : WilliamsonShmoys.maximal_planar_drawing_maximal_extension_exists_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:11:44.604275+00:00
-- url     : https://prove2.me/theorems/074dff57-7f4a-4c58-a6cf-2cf69e78b8d8
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every finite graph with a drawing has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. This removes the finite maximal-extension step from the parent. Independently prove it by considering the finite collection of graphs containing G that have drawings and selecting one with the greatest number of edges; any drawable supergraph of that choice must have the same edges and hence be equal to it. The argument includes empty edge sets and does not require a vertex-count lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_maximal_extension_exists_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
