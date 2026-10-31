-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_edge_ncard__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_edge_ncard__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:25:29.051299+00:00
-- url     : https://prove2.me/theorems/b0c705b6-db22-4d0f-9709-6b9e23813311
-- title:
--   Connect a finite planar drawing without losing edges
-- statement:
--   Given a finite drawn graph with at least three vertices, one can add edges to make it connected while keeping a crossing-free drawing and retaining every original edge. To prove it, join components through the complement of the finite drawing. The size hypothesis ensures the vertex type is nonempty, as required by `SimpleGraph.Connected`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_edge_ncard__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
