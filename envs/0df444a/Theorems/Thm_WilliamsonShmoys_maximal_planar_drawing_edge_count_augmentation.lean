-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_augmentation
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:04:40.448994+00:00
-- url     : https://prove2.me/theorems/cb03e387-c0aa-46cb-87fc-0ed35195de89
-- title:
--   Drawable graphs admit an edge-bounded planar augmentation
-- statement:
--   Every finite graph with at least three vertices that has a drawing satisfying the attached crossing-free arc predicate is contained in a drawable graph with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  sorry
