-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:00:25.258976+00:00
-- url     : https://prove2.me/theorems/992190c8-dc72-46b4-8dda-28fc980251e4
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_0d58a30b_b602_48eb_8495_a2236e2d87f2 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hCard : 3 ≤ Fintype.card V) (hTmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
