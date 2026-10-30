-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_edge_count
-- name    : WilliamsonShmoys.planar_completion_with_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:55:13.006248+00:00
-- url     : https://prove2.me/theorems/1cf55c2d-95d3-4727-9dee-d527daf4cb7b
-- title:
--   Triangulated planar completion on a fixed vertex set
-- statement:
--   Any finite graph with at least three vertices that admits the supplied crossing-free drawing has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This packages the planar augmentation and Euler-counting argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_with_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
