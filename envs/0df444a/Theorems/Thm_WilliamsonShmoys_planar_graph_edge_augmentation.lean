-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_augmentation
-- name    : WilliamsonShmoys.planar_graph_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:00:20.317343+00:00
-- url     : https://prove2.me/theorems/b45029ee-29f3-454e-b7b8-0358d778980c
-- title:
--   Planar graph edge augmentation below the maximal planar bound
-- statement:
--   For a finite simple graph on at least three vertices, a crossing-free drawing and an edge count strictly below 3|V|−6 imply that some strict supergraph on the same vertex type also has a crossing-free drawing. The strict deficit handles the three-vertex boundary, where the maximal planar graph is the triangle. Prove by extending a planar embedding to a maximal simple planar graph, triangulating its faces, and applying Euler’s formula and face-edge incidence counting. The parent uses this to contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hdeficit : U.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧ W ≠ U ∧ WilliamsonShmoys.HasPlanarDrawingOn W := by sorry
