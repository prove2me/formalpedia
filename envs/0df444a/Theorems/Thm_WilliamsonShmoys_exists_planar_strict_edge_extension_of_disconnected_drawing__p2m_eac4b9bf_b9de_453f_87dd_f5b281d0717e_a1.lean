-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a1
-- name    : WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:04.71271+00:00
-- url     : https://prove2.me/theorems/d4845ee8-5b33-4e78-bf1a-df62eb784c7d
-- title:
--   Planar extension joining components of a disconnected drawing
-- statement:
--   Every disconnected finite graph with a drawing as specified admits a planar supergraph on the same vertices containing a new edge between two distinct vertices that were not adjacent. The proof must construct a suitable redrawing or joining arc; it cannot assume an arbitrary arc avoids the existing drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧
      ∃ L : SimpleGraph V,
        K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.Adj u v := by sorry
