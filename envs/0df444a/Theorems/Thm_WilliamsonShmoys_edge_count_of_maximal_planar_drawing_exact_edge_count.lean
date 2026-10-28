-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_exact_edge_count
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:52:52.569053+00:00
-- url     : https://prove2.me/theorems/b1db10ca-2200-4b55-8753-9bc7a07260c1
-- title:
--   Exact edge count for a maximal planar drawing
-- statement:
--   A graph maximal under inclusion among graphs admitting the given planar drawing predicate, with at least three vertices, has exactly `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_exact_edge_count {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * (Fintype.card V : Int) - 6 = (L.edgeSet.ncard : Int) := by sorry
