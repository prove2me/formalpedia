-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_completion_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_completion_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:01:30.987857+00:00
-- url     : https://prove2.me/theorems/0acfe085-6acd-4f83-a7e5-409feb27ddfb
-- title:
--   Drawable completion with the planar maximal edge count
-- statement:
--   Every drawable simple graph on a fixed finite vertex type of size at least three has a drawable supergraph on that same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_completion_419a1fb2_144c_4e12_b921_930e8d46d3d3 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ 3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
