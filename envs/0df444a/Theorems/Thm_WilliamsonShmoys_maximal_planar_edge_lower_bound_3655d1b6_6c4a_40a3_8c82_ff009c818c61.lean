-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_3655d1b6_6c4a_40a3_8c82_ff009c818c61
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_3655d1b6_6c4a_40a3_8c82_ff009c818c61
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T19:15:02.559762+00:00
-- url     : https://prove2.me/theorems/c1e15bf1-b63f-4f20-b9bd-28e95ef42e76
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_3655d1b6_6c4a_40a3_8c82_ff009c818c61 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
