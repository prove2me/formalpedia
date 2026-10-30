-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_v10
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_v10
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:56:41.543969+00:00
-- url     : https://prove2.me/theorems/a04622a0-2e0b-476e-aeb6-c46888fbb24a
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_v10 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) : 3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
