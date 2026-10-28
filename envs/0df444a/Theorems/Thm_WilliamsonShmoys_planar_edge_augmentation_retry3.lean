-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_retry3
-- name    : WilliamsonShmoys.planar_edge_augmentation_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:37:55.759977+00:00
-- url     : https://prove2.me/theorems/bb21d3db-b3d1-449e-b6aa-a10faf738d7d
-- title:
--   Add one edge below the planar maximum
-- statement:
--   If a drawable graph on at least three vertices has fewer than the planar maximum number of edges, one can add exactly one edge and retain a drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_retry3 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 <= Fintype.card V) (hCount : G.edgeSet.ncard < 3 * Fintype.card V - 6) : exists H : SimpleGraph V, G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\ H.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
