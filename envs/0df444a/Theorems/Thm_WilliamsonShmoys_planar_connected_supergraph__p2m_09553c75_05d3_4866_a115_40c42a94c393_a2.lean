-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
-- name    : WilliamsonShmoys.planar_connected_supergraph__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T06:55:05.520092+00:00
-- url     : https://prove2.me/theorems/ce6f5f96-18b4-457b-8f01-9dcd9d3bda8a
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   A graph with at least three vertices and the specified planar drawing has a connected planar supergraph on the same vertex type, retaining every original edge. The edge-count inequality supplies monotonicity for the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V,
      H.Connected ∧
      (∀ ⦃u v : V⦄, U.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      U.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
