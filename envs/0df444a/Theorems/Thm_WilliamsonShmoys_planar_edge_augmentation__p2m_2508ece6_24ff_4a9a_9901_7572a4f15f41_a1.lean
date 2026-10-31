-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
-- name    : WilliamsonShmoys_planar_edge_augmentation__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:21.616054+00:00
-- url     : https://prove2.me/theorems/9b3efef9-88d6-4457-a3f3-6508d18ac1de
-- title:
--   Augmenting a connected planar graph below the edge bound
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices, whose edge count is below 3|V| − 6, has a planar supergraph on the same vertex type that is not a subgraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_augmentation__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : LE.le 3 (Fintype.card V))
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    Exists fun K : SimpleGraph V => And (LE.le G K) (And (WilliamsonShmoys.HasPlanarDrawingOn K) (Not (LE.le K G))) := by sorry
