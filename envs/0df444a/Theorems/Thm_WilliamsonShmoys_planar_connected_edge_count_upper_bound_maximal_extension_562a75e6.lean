-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound_maximal_extension_562a75e6
-- name    : WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_extension_562a75e6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:06:06.426547+00:00
-- url     : https://prove2.me/theorems/eb4fae06-cbaf-45d2-8d56-f2e9a12366e1
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every finite connected drawable simple graph with at least three vertices is contained in a drawable graph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_extension_562a75e6
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
