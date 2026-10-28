-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected_ge3_c00979a8
-- name    : WilliamsonShmoys.maximal_planar_supergraph_connected_ge3_c00979a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:20:03.848985+00:00
-- url     : https://prove2.me/theorems/c25e728a-0d43-4046-b81c-c920af6e6eb3
-- title:
--   Maximal drawable graphs with at least three vertices are connected
-- statement:
--   A drawable graph on at least three vertices that is maximal by inclusion among drawable graphs on those vertices is connected. The three-vertex lower bound and the exact drawing predicate are retained; the proof must use planar separation and the existence of a noncrossing arc joining distinct components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_supergraph_connected_ge3_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ L : SimpleGraph V, H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ H) : H.Connected := by sorry
