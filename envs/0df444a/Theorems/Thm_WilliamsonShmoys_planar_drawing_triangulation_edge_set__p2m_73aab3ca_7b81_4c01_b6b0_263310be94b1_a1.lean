-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_set__p2m_73aab3ca_7b81_4c01_b6b0_263310be94b1_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_edge_set__p2m_73aab3ca_7b81_4c01_b6b0_263310be94b1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:51.898701+00:00
-- url     : https://prove2.me/theorems/6afd414e-9bd5-44bb-abb9-3ce14ecb25d9
-- title:
--   Triangulation edge set extending a planar drawing
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing, there is a set of exactly `3|V| - 6` undirected vertex pairs that contains every graph edge. It is obtained as the edge set of a triangulated planar extension on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_edge_set__p2m_73aab3ca_7b81_4c01_b6b0_263310be94b1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ F : Finset (Sym2 V),
      G.edgeFinset ⊆ F ∧ F.card = 3 * Fintype.card V - 6 := by
  sorry
