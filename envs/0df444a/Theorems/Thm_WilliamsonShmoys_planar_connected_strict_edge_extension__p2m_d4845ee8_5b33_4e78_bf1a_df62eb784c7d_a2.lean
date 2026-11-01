-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_strict_edge_extension__p2m_d4845ee8_5b33_4e78_bf1a_df62eb784c7d_a2
-- name    : WilliamsonShmoys.planar_connected_strict_edge_extension__p2m_d4845ee8_5b33_4e78_bf1a_df62eb784c7d_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:34.004463+00:00
-- url     : https://prove2.me/theorems/e77097f0-d554-40df-987b-21fad16eb667
-- title:
--   Connected planar extension of a disconnected drawing
-- statement:
--   Every finite disconnected graph with the specified planar drawing has a connected planar supergraph on the same vertices that contains a new edge between distinct vertices that were not adjacent before.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_strict_edge_extension__p2m_d4845ee8_5b33_4e78_bf1a_df62eb784c7d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧
      ∃ L : SimpleGraph V,
        K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
          L.Adj u v ∧ L.Connected := by sorry
