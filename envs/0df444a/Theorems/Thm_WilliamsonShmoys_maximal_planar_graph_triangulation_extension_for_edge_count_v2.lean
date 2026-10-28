-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_triangulation_extension_for_edge_count_v2
-- name    : WilliamsonShmoys.maximal_planar_graph_triangulation_extension_for_edge_count_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:54:32.264484+00:00
-- url     : https://prove2.me/theorems/0463fea4-ae86-4871-b6ed-fe97a1f7a12a
-- title:
--   Triangulation extension with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set of size at least three is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_triangulation_extension_for_edge_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      Set.Subset Q.edgeSet R.edgeSet ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
