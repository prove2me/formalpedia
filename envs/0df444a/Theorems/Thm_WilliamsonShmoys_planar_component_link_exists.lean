-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_link_exists
-- name    : WilliamsonShmoys.planar_component_link_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:50:18.635765+00:00
-- url     : https://prove2.me/theorems/add762e5-35a4-4393-a063-7af1096b0bd6
-- title:
--   Planar drawing permits a link between components
-- statement:
--   For a disconnected graph with the stated finite ordered vertex type and drawing, construct a planar supergraph on the same vertices that contains an edge joining two vertices that were in different components. The component-count decrease is deliberately left to a separate graph-theoretic lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_link_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hDisconnected : ¬ Y.Connected) :
    ∃ (Z : SimpleGraph V), Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∃ u v, ¬ Y.Reachable u v ∧ Z.Adj u v := by sorry
