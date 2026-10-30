-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_edge_count_05b21acc_4700_43ee_9041_67ebfdbea9d3
-- name    : WilliamsonShmoys.planar_completion_with_exact_edge_count_05b21acc_4700_43ee_9041_67ebfdbea9d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:01:30.115492+00:00
-- url     : https://prove2.me/theorems/a5b971c8-fa46-4d98-80c3-63add8b8353a
-- title:
--   Planar completion with exact edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is a subgraph, on the same vertex set, of a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_with_exact_edge_count_05b21acc_4700_43ee_9041_67ebfdbea9d3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
