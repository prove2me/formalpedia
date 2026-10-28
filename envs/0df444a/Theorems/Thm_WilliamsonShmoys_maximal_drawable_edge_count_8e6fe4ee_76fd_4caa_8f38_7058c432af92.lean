-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_8e6fe4ee_76fd_4caa_8f38_7058c432af92
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_8e6fe4ee_76fd_4caa_8f38_7058c432af92
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:44:39.034036+00:00
-- url     : https://prove2.me/theorems/401c0882-1ef1-411b-99bc-318038132e37
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   If `H` is drawable and maximal among drawable supergraphs, then every subgraph `K` of `H` has at most as many edges as `H`, and when there are at least three vertices, `H` has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_8e6fe4ee_76fd_4caa_8f38_7058c432af92 {V : Type} [Fintype V] [LinearOrder V] (K H : SimpleGraph V) (hKH : K ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
