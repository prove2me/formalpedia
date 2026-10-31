-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_spanning_tree_extension
-- name    : WilliamsonShmoys.planar_drawing_spanning_tree_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:14:58.977554+00:00
-- url     : https://prove2.me/theorems/cce0a931-e014-4049-a371-91a36295465a
-- title:
--   Connected spanning subgraph extension of a planar drawing
-- statement:
--   Every finite drawing satisfying the packaged planar arc conditions has a planar supergraph containing both the original graph and a connected spanning subgraph. The augmented graph has at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_spanning_tree_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H T : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      T.Connected ∧
      (∀ u v, T.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
