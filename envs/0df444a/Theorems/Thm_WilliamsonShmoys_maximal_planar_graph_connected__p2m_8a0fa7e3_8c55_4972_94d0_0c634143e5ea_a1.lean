-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T11:49:39.468955+00:00
-- url     : https://prove2.me/theorems/0d71806b-1bff-4247-911b-0bb3ff02c978
-- title:
--   An inclusion-maximal planar graph on at least three vertices is connected
-- statement:
--   If a graph on at least three vertices has a crossing-free drawing and cannot be enlarged by adding edges while preserving such a drawing, then it is connected. If disconnected, connect two components with a new arc avoiding the finite drawing to contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊆ K.edgeSet → K.edgeSet = H.edgeSet) :
    H.Connected := by sorry
