-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5
-- name    : WilliamsonShmoys.planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:15.420336+00:00
-- url     : https://prove2.me/theorems/c96f9502-b6a7-485d-895c-b4be9d2d28fa
-- title:
--   Triangulation extension edge count for a drawable graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is 3|V| − 6. The edge-count expression explicitly installs the classical adjacency decision procedure for the extension graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  sorry
