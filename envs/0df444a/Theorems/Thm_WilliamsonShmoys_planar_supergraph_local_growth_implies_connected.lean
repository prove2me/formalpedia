-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_local_growth_implies_connected
-- name    : WilliamsonShmoys.planar_supergraph_local_growth_implies_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:09:10.060222+00:00
-- url     : https://prove2.me/theorems/ea876606-ae0d-43db-ade6-f4b12500d1cd
-- title:
--   Maximal planar supergraphs are connected under local growth
-- statement:
--   If every disconnected planar supergraph of a planar graph can be extended to a planar supergraph with strictly more edges, then there is a connected planar supergraph containing the original graph. Choose a maximum-edge graph among the finitely many supergraphs on the fixed finite vertex type; local growth rules out its being disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_local_growth_implies_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hGrow : ∀ G : SimpleGraph V, K ≤ G →
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ G' : SimpleGraph V, G ≤ G' ∧
        WilliamsonShmoys.HasPlanarDrawingOn G' ∧
        G.edgeSet.ncard < G'.edgeSet.ncard) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
