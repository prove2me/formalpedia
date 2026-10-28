-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_triangulation_augmentation
-- name    : WilliamsonShmoys.planar_simple_graph_triangulation_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:59:19.210851+00:00
-- url     : https://prove2.me/theorems/bbac830c-bdd7-4ce0-b60c-576a21574995
-- title:
--   Augment a finite planar simple graph to an extremal supergraph
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices is contained in a planar simple graph on the same vertices with exactly `3|V| - 6` edges. The drawing must be preserved while adding edges; at three vertices the extremal graph is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_triangulation_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
